//! This module contains anything needed to work with the state of the application. The state is a
//! type, which supposed to be modified by [Change](self::Change).

use std::sync::{Arc, Mutex};

pub use undo::{Action, History};

/// Implement this trait for your state.
pub trait State: Default {
    /// Action's output.
    type Output;

    /// The action type (i.e. enumeration of changes) for this state.
    type Changes: Changes<State = Self, Output = Self::Output>;

    /// Apply [Change](self::Change) to the state.
    fn apply<C>(&mut self, change: C) -> Self::Output
    where
        C: Change + Into<Self::Changes> + From<Self::Changes>,
    {
        self.apply_action(change.into())
    }

    /// Apply `Self::Changes`.
    fn apply_action(&mut self, action: Self::Changes) -> Self::Output {
        let history = self.history();
        let mut history = history.lock().unwrap();

        history.apply(self, action)
    }

    /// Undo the last change.
    fn undo(&mut self) -> Option<Self::Output> {
        let history = self.history();
        let mut history = history.lock().unwrap();

        history.undo(self)
    }

    /// Redo the last change.
    fn redo(&mut self) -> Option<Self::Output> {
        let history = self.history();
        let mut history = history.lock().unwrap();

        history.redo(self)
    }

    /// Get [History](undo::History).
    fn history(&self) -> Arc<Mutex<History<Self::Changes>>>;
}

/// Enumeration of all the changes for state. Usually you'd like to generate it using
/// [`impl_changes`!](self::impl_changes) macro.
pub trait Changes: Action<Target = <Self as Changes>::State> + Clone + Default {
    /// The state.
    type State: State;
    /// The description/documentation of a single change.
    fn description(&self) -> Option<&'static str>;
}

/// `Change` is an abstraction of a state change (i.e. it's a representation of a single change in
/// the state).
pub trait Change: std::fmt::Debug {
    /// The state, which is modified by this command.
    type State: State;

    /// The result of the change.
    type Output;

    /// Dispatch the change (i.e. modify the state).
    fn apply(&mut self, _state: &mut Self::State) -> Self::Output;

    /// Make the state back before the change applied.
    fn undo(&mut self, _state: &mut Self::State) -> Self::Output;

    /// Get the description of `Change` (useful for command listing/searching in the app).
    fn description(&self) -> &'static str;
}

/// Generate actions enumeration for listed changes.
///
/// The type is public and called `Changes`. So you can reference it later inside your state.
/// Usually, you wouldn't need use it directly. It's expected you'll use `Change` implementation
/// with `From` and `Into` traits.
///
/// - the first argument is the type of the state, which is modified by these actions
/// - the second argument is the type of the change result
/// - the rest is the changes types
#[macro_export]
macro_rules! impl_changes {
    ($state:ty, $change_result:ty, $($change:ident),+) => {
        #[allow(missing_docs)]
        #[derive(Debug, Default, Clone, Serialize, Deserialize)]
        pub enum Changes {
            $($change($change),)*
                #[default]
                Default,
        }

        impl $crate::state::Changes for Changes {
            type State = $state;

            fn description(&self) -> Option<&'static str> {
                match self {
                    $(Self::$change(change) => Some(change.description()),)*
                        Self::Default => None,
                }
            }
        }

        impl $crate::state::Action for Changes {
            type Target = $state;
            type Output = $change_result;

            fn apply(&mut self, state: &mut Self::Target) -> Self::Output {
                match self {
                    $(Changes::$change(change) => change.apply(state),)*
                        _ => unreachable!(),
                }
            }

            fn undo(&mut self, state: &mut Self::Target) -> Self::Output {
                match self {
                    $(Changes::$change(change) => change.undo(state),)*
                        #[allow(unreachable_patterns)]
                        _ => unreachable!(),
                }
            }
        }

        $(
            impl From<$change> for Changes {
                fn from(change: $change) -> Self {
                    Changes::$change(change)
                }
            }

            impl From<Changes> for $change {
                fn from(actions: Changes) -> Self {
                    match actions {
                        Changes::$change(change) => change,
                        #[allow(unreachable_patterns)]
                        _ => unreachable!(),
                    }
                }
            }
        )*
    }
}

/// Implement a wrapper (`enum`) around change output.
///
/// It helps you to make a single result for all your changes and conveniently convert it between a
/// type and an enumeration variant. The first argument is the name of the resulting `enum` and the
/// rest are `tuples` of (`<enum_name>`, `type`).
///
/// # Example
///
/// ```
/// # use spark_app::impl_change_output;
///
/// impl_change_output!(ChangeOutput, (F32, f32), (Empty, ()));
///
/// let expected: f32 = ChangeOutput::F32(1.0).into();
///
/// assert_eq!(expected, 1.0);
///
/// let expected: ChangeOutput = ().into();
///
/// matches!(expected, Empty);
/// ```
#[macro_export]
macro_rules! impl_change_output {
    ($name:ident, $(($variant:ident, $inner:ty)),+$(,)?) => {
        #[allow(missing_docs)]
        #[derive(Debug)]
        pub enum $name {
            $($variant($inner),)*
        }

        $(
            impl From<$inner> for $name {
                fn from(inner: $inner) -> Self {
                    Self::$variant(inner)
                }
            }

            impl From<$name> for $inner {
                fn from(output: $name) -> Self {
                    match output {
                        $name::$variant(inner) => inner,
                        #[allow(unreachable_patterns)]
                        _ => unreachable!(),
                    }
                }
            }
        )*
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[allow(missing_docs, unreachable_pub)]
    mod mock;
    use mock::*;

    #[test]
    fn state_history_works() {
        let mut document = Document::default();
        document.apply(Add(42));
        assert_eq!(document.value, 42);

        document.apply(Add(27));
        assert_eq!(document.value, 69);

        document.apply(Sub(12));
        assert_eq!(document.value, 57);

        document.undo();
        assert_eq!(document.value, 69);

        document.undo();
        assert_eq!(document.value, 42);

        document.undo();
        assert_eq!(document.value, 0);

        document.redo();
        assert_eq!(document.value, 42);

        document.redo();
        assert_eq!(document.value, 69);

        document.redo();
        assert_eq!(document.value, 57);
    }
}
