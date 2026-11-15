/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Separation axioms for the type tags `Multiplicative` and `Additive`

The type tags `Multiplicative X` and `Additive X` carry the topology of `X`, and Mathlib records
that compactness, local compactness and total disconnectedness pass to them. This file does the
same for the separation axioms `R1Space`, `T1Space`, and `T2Space`, which are what inner-regular
integration and continuous homomorphisms on a type tag need: compact sets are closed or measurable
in an `R1` space, the kernel of a continuous homomorphism into a `T1` group is closed, and two
continuous maps into a `T2` space agreeing on a dense set agree.

These instances are needed as soon as a multiplicative or additive type tag is put on a group whose
separation is known only from an ambient construction, for instance a quotient of a topological
module by a closed submodule, rather than from a topological-group instance chain.
-/

public section

variable {X : Type*} [TopologicalSpace X]

instance [R1Space X] : R1Space (Multiplicative X) := ‹R1Space X›

instance [R1Space X] : R1Space (Additive X) := ‹R1Space X›

instance [T1Space X] : T1Space (Multiplicative X) := ‹T1Space X›

instance [T1Space X] : T1Space (Additive X) := ‹T1Space X›

instance [T2Space X] : T2Space (Multiplicative X) := ‹T2Space X›

instance [T2Space X] : T2Space (Additive X) := ‹T2Space X›
