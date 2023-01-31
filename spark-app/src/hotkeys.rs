//! Hotkeys management system. You just need to keep it in your app instance and call
//! `HotkeysManager::handle` from your event loop.

use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::marker::PhantomData;

use serde::{Deserialize, Serialize};

use crate::state::{Change, Changes, State as StateTrait};

/// Hotkeys map and handler.
#[derive(Debug, Deserialize, Serialize)]
pub struct HotkeysManager<Hotkey, Action, Output, State>
where
    Hotkey: Eq + Hash,
    Action: Changes,
    State: StateTrait<Changes = Action, Output = Output>,
{
    map: HashMap<Hotkey, Action>,
    reserved: HashSet<Hotkey>,
    __state: PhantomData<State>,
}

impl<Hotkey, Action, Output, State> Default for HotkeysManager<Hotkey, Action, Output, State>
where
    Hotkey: Eq + Hash + Deserialize<'static>,
    Action: Changes,
    State: StateTrait<Changes = Action, Output = Output>,
{
    fn default() -> Self {
        Self {
            map: HashMap::new(),
            reserved: HashSet::new(),
            __state: PhantomData,
        }
    }
}

impl<Hotkey, Action, Output, State> HotkeysManager<Hotkey, Action, Output, State>
where
    Hotkey: Eq + Hash + Deserialize<'static>,
    Action: Changes,
    State: StateTrait<Changes = Action, Output = Output>,
{
    /// Initialize `HotkeysManager` with reserved hotkeys (i.e. which you wouldn't like to be
    /// assigned). Usually it's system hotkeys like for undo/redo, copy, paste, etc.
    pub fn with_reserved(mut self, reserved: HashSet<Hotkey>) -> Self {
        self.reserved = reserved;
        self
    }

    /// Add a hotkey to the map and associate a change which will be applied to the state.
    ///
    /// Returns `false` if the hotkey already assigned.
    pub fn register_hotkey<C>(&mut self, hotkey: Hotkey, change: C) -> bool
    where
        C: Change + Into<State::Changes>,
    {
        !self.reserved.contains(&hotkey)
            && !self.map.contains_key(&hotkey)
            // NOTE: we could use `.is_none` here, but... just in case
            && {self.map.insert(hotkey, change.into()); true}
    }

    /// Remove the hotkey from the map.
    pub fn unregister_hotkey(&mut self, hotkey: &Hotkey) {
        self.map.remove(hotkey);
    }

    /// Call it to handle the hotkey.
    pub fn handle(
        &mut self,
        hotkey: &Hotkey,
        state: &mut State,
        mut result_handler: impl FnMut(Output),
    ) {
        if self.reserved.contains(hotkey) {
            return;
        }

        if let Some(action) = self.map.get(hotkey) {
            result_handler(state.apply_action(action.clone()));
        }
    }

    /// Call a function for each key-action mapping.
    pub fn for_each(&self, mut f: impl FnMut(&Hotkey, Action)) {
        self.map.iter().for_each(|(k, v)| f(k, v.clone()));
    }

    /// Get a string describing what the hotkey does.
    pub fn describe_hotkey(&self, hotkey: &Hotkey) -> Option<&'static str> {
        self.map.get(hotkey).and_then(|action| action.description())
    }
}
