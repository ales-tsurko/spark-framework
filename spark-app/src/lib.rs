//! This library contains abstractions to implement an application with a state manager, editing
//! history (undo/redo), hotkeys manager, settings manager, etc. It doesn't dependent on any GUI
//! framework. It's event-based — every change of a state is represented by a particular type, which
//! implements [`state::Change`](crate::state::Change).

#![warn(
    clippy::all,
    deprecated_in_future,
    missing_docs,
    unused_import_braces,
    unused_labels,
    unused_lifetimes,
    unused_qualifications,
    unreachable_pub
)]

use std::hash::Hash;
use std::sync::{Arc, Mutex};

use serde::{Deserialize, Serialize};

pub mod hotkeys;
pub mod state;

/// The application.
#[derive(Debug, Deserialize, Serialize)]
pub struct App<Hotkey, Action, Output, State>
where
    Hotkey: Eq + Hash,
    Action: state::Changes,
    State: state::State<Changes = Action, Output = Output>,
{
    /// Hotkeys manager.
    pub hotkeys: Arc<Mutex<hotkeys::HotkeysManager<Hotkey, Action, Output, State>>>,
    /// The application state.
    pub state: Arc<Mutex<State>>,
}

impl<Hotkey, Action, Output, State> Default for App<Hotkey, Action, Output, State>
where
    Hotkey: Eq + Hash + Deserialize<'static>,
    Action: state::Changes,
    State: state::State<Changes = Action, Output = Output>,
{
    fn default() -> Self {
        Self {
            hotkeys: Default::default(),
            state: Default::default(),
        }
    }
}

impl<Hotkey, Action, Output, State> App<Hotkey, Action, Output, State>
where
    Hotkey: Eq + Hash + Deserialize<'static>,
    Action: state::Changes,
    State: state::State<Changes = Action, Output = Output>,
{
    /// Set the hotkeys manager.
    pub fn with_hotkeys_manager(
        mut self,
        hotkeys: hotkeys::HotkeysManager<Hotkey, Action, Output, State>,
    ) -> Self {
        self.hotkeys = Arc::new(Mutex::new(hotkeys));
        self
    }

    /// A shortcut for [`HotkeysManager::handle`](crate::hotkeys::HotkeysManager::handle).
    pub fn handle_hotkey(&self, hotkey: &Hotkey, result_handler: impl FnMut(Output)) {
        let mut state = self.state.lock().unwrap();
        self.hotkeys
            .lock()
            .unwrap()
            .handle(hotkey, &mut state, result_handler);
    }
}
