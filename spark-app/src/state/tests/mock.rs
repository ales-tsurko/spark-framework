use serde::{Deserialize, Serialize};

use super::*;

#[derive(Debug, Default)]
pub struct Document {
    pub(crate) value: i32,
    history: Arc<Mutex<History<Changes>>>,
}

impl State for Document {
    type Changes = Changes;
    type Output = ChangeOutput;

    fn history(&self) -> Arc<Mutex<History<Self::Changes>>> {
        self.history.clone()
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Add(pub(crate) i32);
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Sub(pub(crate) i32);

impl Change for Add {
    type State = Document;
    type Output = ChangeOutput;

    fn apply(&mut self, state: &mut Self::State) -> Self::Output {
        state.value += self.0;
        self.0.into()
    }

    fn undo(&mut self, state: &mut Self::State) -> Self::Output {
        state.value -= self.0;
        self.0.into()
    }

    fn description(&self) -> &'static str {
        "Add a number"
    }
}

impl Change for Sub {
    type State = Document;
    type Output = ChangeOutput;

    fn apply(&mut self, state: &mut Self::State) -> Self::Output {
        state.value -= self.0;
        self.0.into()
    }

    fn undo(&mut self, state: &mut Self::State) -> Self::Output {
        state.value += self.0;
        self.0.into()
    }

    fn description(&self) -> &'static str {
        "Sub a number"
    }
}

impl_changes!(Document, ChangeOutput, Add, Sub);
impl_change_output!(ChangeOutput, (I32, i32));
