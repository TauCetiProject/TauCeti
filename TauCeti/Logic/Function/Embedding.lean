/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Embedding.Basic

/-!
# Embeddings of distinct pairs and injective tuples

A vertex embedding acts coordinatewise on ordered distinct pairs and on injective tuples.
These embeddings allow finite supports and their cardinalities to be transported between hosts.
-/

public section

namespace Function.Embedding

variable {ι V W : Type*}

/-- Apply an embedding to both vertices of an ordered distinct pair. -/
def distinctPairMap (f : V ↪ W) :
    {p : V × V // p.1 ≠ p.2} ↪ {p : W × W // p.1 ≠ p.2} :=
  (f.prodMap f).subtypeMap fun {_} hp ↦ fun h ↦ hp (f.injective h)

@[simp]
theorem distinctPairMap_apply (f : V ↪ W) (p : {p : V × V // p.1 ≠ p.2}) :
    (f.distinctPairMap p).1 = (f p.1.1, f p.1.2) := (rfl)

/-- Postcompose an injective tuple with a vertex embedding. -/
def injectiveMap (f : V ↪ W) :
    {x : ι → V // Function.Injective x} ↪ {x : ι → W // Function.Injective x} :=
  f.arrowCongrRight.subtypeMap fun {_} hx ↦ f.injective.comp hx

@[simp]
theorem injectiveMap_apply (f : V ↪ W) (x : {x : ι → V // Function.Injective x}) :
    (f.injectiveMap x).1 = f ∘ x.1 := (rfl)

end Function.Embedding
