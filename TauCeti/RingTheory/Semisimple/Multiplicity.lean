/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.SimpleModule.Isotypic
public import TauCeti.RingTheory.CompositionSeries.Additivity
public import TauCeti.RingTheory.Semisimple.Schur
public import TauCeti.RingTheory.Semisimple.RegularIsotypicComponent

/-!
# The multiplicity of a simple module, as the dimension of a hom space

Let `A` be an algebra over a field `k` and let `S` be a simple `A`-module, finite-dimensional over
`k`. If a module `M` is written as a finite direct sum of simple
modules, the number of summands isomorphic to `S` is the **multiplicity** of `S` in `M`.  Written
that way the multiplicity refers to a chosen decomposition. Over an algebraically closed field
this file identifies it with the manifestly choice-free number

`Module.finrank k (S →ₗ[A] M)`,

so that the multiplicity is an invariant of `M` and needs no decomposition to be defined.

The proof is Schur's lemma plus additivity.  A hom space out of `S` into a finite product splits
as the product of the hom spaces into the factors, and each factor contributes `1` or `0`
according as it is or is not isomorphic to `S`.  Those two values are the dimension forms of
Schur's lemma, `TauCeti.finrank_linearMap_eq_one_of_nonempty_linearEquiv` and
`TauCeti.finrank_linearMap_eq_zero_of_isEmpty_linearEquiv`, proved in
`TauCeti/RingTheory/Semisimple/Schur.lean` alongside the transport of a hom space along an
isomorphism of its target, `TauCeti.homCongrRight`.

Over an arbitrary field, an isomorphic factor instead contributes
`finrank k (Module.End A S)`.  The corresponding scaled multiplicity formula is enough to recover
the number of factors, since this endomorphism algebra has positive dimension. Constituent
detection and hom-space reconstruction therefore need no algebraic closure. Multiplicity
invariance is proved over arbitrary rings by identifying the factor count with the
Jordan-Hölder multiplicity.

The hom-space dimension results are stated for a `k`-algebra `A` and `A`-modules that are
`k`-modules compatibly. For `A = k[G]`, the hom space is the space of intertwiners. The
reconstruction result from simple-module classes needs only a semisimple ring, while
reconstruction from hom-space dimensions returns to the finite-dimensional `k`-algebra setting.

## Main results

* `TauCeti.finrank_linearMap_eq_natCard_of_linearEquiv_pi`: **the multiplicity theorem.**  If
  `M ≃ₗ[A] ∀ i, N i` with every `N i` simple, then `finrank k (S →ₗ[A] M)` is the number of
  indices `i` with `N i ≅ S`.
* `LinearEquiv.finrank_linearMap_eq_natCard_mul_finrank_end`: over an arbitrary field, the same
  count is multiplied by the dimension of the division algebra `End_A(S)`; the literal product
  form is `TauCeti.finrank_linearMap_pi_eq_natCard_mul_finrank_end`.
* `TauCeti.jordanHolderMultiplicity_pi_eq_natCard`: over any ring, the count of simple factors
  is the Jordan-Hölder multiplicity.
* `TauCeti.natCard_eq_natCard_of_linearEquiv_pi`: equivalent finite products of simple modules
  over any ring have equally many factors isomorphic to `S`; applied to two decompositions of
  one module, this says that the multiplicity is well defined.
* `TauCeti.nonempty_linearEquiv_pi_of_natCard_eq`: conversely, two finite products of simple
  modules are linearly equivalent when their numbers of factors in every simple-module class
  agree.
* `TauCeti.nonempty_linearEquiv_of_finrank_linearMap_eq`: finite modules over a finite-dimensional
  semisimple algebra are linearly equivalent when every simple left ideal has the same hom-space
  dimension into them.
* `TauCeti.natCard_linearMap_eq_pow_jordanHolderMultiplicity`: over any ring, maps from a
  finitely generated semisimple module `M` to a simple module `S` number `#End(S) ^ [M : S]`.
* `TauCeti.IsSemisimpleModule.nonempty_linearEquiv_of_jordanHolderMultiplicity_eq`: over any ring,
  finitely generated semisimple modules with the same Jordan-Hölder multiplicities are isomorphic.
* `TauCeti.finrank_linearMap_pos_iff_exists_nonempty_linearEquiv`: the multiplicity is positive
  exactly when `S` occurs among the factors, so the hom space detects the constituents.
* `TauCeti.finrank_linearMap_eq_natCard_of_linearEquiv_pi_const`: the isotypic case, where `M` is
  a power of `S` itself and the multiplicity is the number of copies.
* `TauCeti.nonempty_linearEquiv_isotypicComponent`: **the isotypic component is the power of its
  type with exponent the multiplicity**, `isotypicComponent A M S ≃ₗ[A] Fin m → S` for
  `m = finrank k (S →ₗ[A] M)`, and
  `TauCeti.finrank_isotypicComponent`: consequently `dim (isotypicComponent A M S) = m · dim S`.
* `TauCeti.finrank_linearMap_pos_of_ne_bot`: for a finite-dimensional `M`, the hom space out of
  any nonzero submodule is positive-dimensional.  This asks for neither simplicity nor an
  algebraically closed field, so it lives apart from the results above.

## The isotypic component

Mathlib's `isotypicComponent A M S` is the sum of the submodules of `M` isomorphic to `S`, and
`IsIsotypicOfType.linearEquiv_fun` writes it as a finite power of `S` once `S` is simple and `M` is
finite-dimensional.  What the multiplicity theorem adds is the value of the exponent: every
`A`-linear map out of `S` lands in the isotypic component
(`LinearMap.apply_mem_isotypicComponent`), so `TauCeti.linearMapIsotypicComponentEquiv` identifies
their hom spaces out of `S`, and the count above identifies the exponent with
`finrank k (S →ₗ[A] M)`. This is the decomposition-free description of the component that a
multiplicity computation needs.

## Implementation notes

The index set of a decomposition is counted with `Nat.card` of a subtype rather than with a
`Finset.filter`, so that no `DecidablePred` instance enters the statements; the proofs introduce
classical decidability and a `Fintype` structure locally.

The semisimple-ring reconstruction theorem counts factors by `simpleModuleClass`; the hom-space
reconstruction theorem converts those class fibres to the `Nonempty (S ≃ₗ[A] N i)` convention of
the multiplicity theorem using `simpleModuleClass_eq_mk_iff`.

Over an arbitrary ring, where simple modules need not embed in the ring, the factors of a
finitely generated semisimple module are instead taken to be quotients `R ⧸ m` by maximal left
ideals, and are matched up to isomorphism directly; maps out of such a module into a simple module
are counted with `Nat.card`, which needs no base field.

The dimension formulas assume simplicity of `S` and finite dimensionality over `k`. The
multiplicity theorem takes the decomposition of `M` as data; existence of a decomposition is the
separate semisimplicity input. The ring-general factor-count statements need neither a base field
nor simplicity of the module whose occurrences are counted.

## References

See C. W. Curtis and I. Reiner, *Representation Theory of Finite Groups and Associative Algebras*,
§25, or J.-P. Serre, *Linear Representations of Finite Groups*, §2.
-/

public section

namespace TauCeti

/-! ### The multiplicity of a simple module in a finite direct sum -/

section Multiplicity

section ArbitraryField

variable {k A S : Type*} [Field k] [Ring A] [Algebra k A]
variable [AddCommGroup S] [Module k S] [Module A S] [IsScalarTower k A S] [IsSimpleModule A S]
variable [FiniteDimensional k S]
variable {ι : Type*} [Finite ι] {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module k (N i)]
  [∀ i, Module A (N i)] [∀ i, IsScalarTower k A (N i)] [∀ i, IsSimpleModule A (N i)]

/-- **The multiplicity formula over an arbitrary field.** The dimension of the space of maps from
a simple module `S` into a finite product of simple modules is the number of factors isomorphic
to `S`, multiplied by the dimension of the division algebra `End_A(S)`. -/
theorem finrank_linearMap_pi_eq_natCard_mul_finrank_end :
    Module.finrank k (S →ₗ[A] ∀ i, N i) =
      Nat.card {i // Nonempty (S ≃ₗ[A] N i)} * Module.finrank k (Module.End A S) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  have hfin : ∀ i, FiniteDimensional k (S →ₗ[A] N i) := fun _ ↦
    finiteDimensional_linearMap_of_isSimpleModule
  have hpi : Module.finrank k (S →ₗ[A] ∀ i, N i) =
      ∑ i, Module.finrank k (S →ₗ[A] N i) := by
    rw [← (LinearEquiv.linearMapPi (R := A) (M₂ := S) (φ := N) k).finrank_eq]
    exact Module.finrank_pi_fintype k
  have hval : ∀ i, Module.finrank k (S →ₗ[A] N i) =
      if Nonempty (S ≃ₗ[A] N i) then Module.finrank k (Module.End A S) else 0 := by
    intro i
    split_ifs with hi
    · exact (homCongrRight k (S := S) hi.some).finrank_eq.symm
    · exact finrank_linearMap_eq_zero_of_isEmpty_linearEquiv (not_nonempty_iff.mp hi)
  rw [hpi, Finset.sum_congr rfl fun i _ ↦ hval i]
  simp [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.sum_ite]

/-- The multiplicity formula over an arbitrary field, for a module given with a finite
simple decomposition. Each copy of `S` contributes the dimension of `End_A(S)`. -/
theorem _root_.LinearEquiv.finrank_linearMap_eq_natCard_mul_finrank_end {M : Type*}
    [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    (e : M ≃ₗ[A] ∀ i, N i) :
    Module.finrank k (S →ₗ[A] M) =
      Nat.card {i // Nonempty (S ≃ₗ[A] N i)} * Module.finrank k (Module.End A S) := by
  rw [(homCongrRight k (S := S) e).finrank_eq,
    finrank_linearMap_pi_eq_natCard_mul_finrank_end (k := k)]

end ArbitraryField

variable {k A S : Type*} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [AddCommGroup S] [Module k S] [Module A S] [IsScalarTower k A S] [IsSimpleModule A S]
variable [FiniteDimensional k S]
variable {ι : Type*} [Finite ι] {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module k (N i)]
  [∀ i, Module A (N i)] [∀ i, IsScalarTower k A (N i)] [∀ i, IsSimpleModule A (N i)]

/-- **The multiplicity theorem for a product of simple modules.**  The dimension of the space of
`A`-linear maps from a simple module `S` into a finite product of simple modules counts the
factors isomorphic to `S`. -/
theorem finrank_linearMap_pi_eq_natCard :
    Module.finrank k (S →ₗ[A] ∀ i, N i) = Nat.card {i // Nonempty (S ≃ₗ[A] N i)} := by
  rw [finrank_linearMap_pi_eq_natCard_mul_finrank_end (k := k),
    finrank_linearMap_eq_one_of_nonempty_linearEquiv (LinearEquiv.refl A S), mul_one]

/-- **The multiplicity theorem.**  If `M` decomposes as a finite direct sum of simple modules
`N i`, then the dimension of the space of `A`-linear maps from a simple module `S` into `M` is
the number of factors isomorphic to `S`.

Only the right-hand side mentions the decomposition, so this is the statement that the
multiplicity of `S` in `M` is an invariant of `M`; see
`TauCeti.natCard_eq_natCard_of_linearEquiv_pi`. -/
theorem finrank_linearMap_eq_natCard_of_linearEquiv_pi {M : Type*} [AddCommGroup M] [Module k M]
    [Module A M] [IsScalarTower k A M] (e : M ≃ₗ[A] ∀ i, N i) :
    Module.finrank k (S →ₗ[A] M) = Nat.card {i // Nonempty (S ≃ₗ[A] N i)} := by
  rw [e.finrank_linearMap_eq_natCard_mul_finrank_end (k := k),
    finrank_linearMap_eq_one_of_nonempty_linearEquiv (LinearEquiv.refl A S), mul_one]

omit [IsAlgClosed k] in
/-- A module with a finite decomposition into simple modules has a finite-dimensional space of
maps from a finite-dimensional simple module into it. -/
theorem finiteDimensional_linearMap_of_linearEquiv_pi {M : Type*} [AddCommGroup M] [Module k M]
    [Module A M] [IsScalarTower k A M] (e : M ≃ₗ[A] ∀ i, N i) :
    FiniteDimensional k (S →ₗ[A] M) := by
  have hfin : ∀ i, FiniteDimensional k (S →ₗ[A] N i) := fun _ ↦
    finiteDimensional_linearMap_of_isSimpleModule
  have hpi : FiniteDimensional k (S →ₗ[A] ∀ i, N i) :=
    Module.Finite.equiv (LinearEquiv.linearMapPi (R := A) (M₂ := S) (φ := N) k)
  exact Module.Finite.equiv (homCongrRight k (S := S) e).symm

omit [IsAlgClosed k] in
/-- **A hom space detects a constituent.**  There is a nonzero `A`-linear map from the simple
module `S` into `M` exactly when `S` occurs among the simple factors of `M`. -/
theorem finrank_linearMap_pos_iff_exists_nonempty_linearEquiv {M : Type*} [AddCommGroup M]
    [Module k M] [Module A M] [IsScalarTower k A M] (e : M ≃ₗ[A] ∀ i, N i) :
    0 < Module.finrank k (S →ₗ[A] M) ↔ ∃ i, Nonempty (S ≃ₗ[A] N i) := by
  have : Module.Finite k (Module.End A S) :=
    finiteDimensional_linearMap_of_isSimpleModule
  have : Nontrivial S := IsSimpleModule.nontrivial A S
  rw [e.finrank_linearMap_eq_natCard_mul_finrank_end (k := k),
    mul_pos_iff_of_pos_right
      (Module.finrank_pos : 0 < Module.finrank k (Module.End A S)), Nat.card_pos_iff,
    nonempty_subtype]
  exact and_iff_left inferInstance

end Multiplicity

/-! ### Multiplicity invariance over arbitrary rings -/

section RingMultiplicity

variable {A S : Type*} [Ring A] [AddCommGroup S] [Module A S]
variable {ι : Type*} [Finite ι] {N : ι → Type*} [∀ i, AddCommGroup (N i)]
  [∀ i, Module A (N i)] [∀ i, IsSimpleModule A (N i)]

/-- The Jordan-Hölder multiplicity in a finite product of simple modules counts the factors
isomorphic to the given module. -/
theorem jordanHolderMultiplicity_pi_eq_natCard :
    jordanHolderMultiplicity A (∀ i, N i) S = Nat.card {i // Nonempty (S ≃ₗ[A] N i)} := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  rw [jordanHolderMultiplicity_pi]
  have hval (i : ι) : jordanHolderMultiplicity A (N i) S =
      if Nonempty (S ≃ₗ[A] N i) then 1 else 0 := by
    split_ifs with h
    · exact jordanHolderMultiplicity_eq_one_of_isSimpleModule_of_linearEquiv S h.some.symm
    · exact jordanHolderMultiplicity_eq_zero_of_isEmpty_linearEquiv_of_isSimpleModule S
        ⟨fun e ↦ h ⟨e.symm⟩⟩
  simp_rw [hval]
  simp [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- Equivalent finite products of simple modules contain equally many copies of every module.
This is Jordan-Hölder invariance over an arbitrary ring, without a choice of base field. -/
theorem natCard_eq_natCard_of_linearEquiv_pi {κ : Type*} [Finite κ] {P : κ → Type*}
    [∀ j, AddCommGroup (P j)] [∀ j, Module A (P j)] [∀ j, IsSimpleModule A (P j)]
    (e : (∀ i, N i) ≃ₗ[A] ∀ j, P j) :
    Nat.card {i // Nonempty (S ≃ₗ[A] N i)} = Nat.card {j // Nonempty (S ≃ₗ[A] P j)} := by
  rw [← jordanHolderMultiplicity_pi_eq_natCard, ← jordanHolderMultiplicity_pi_eq_natCard]
  exact jordanHolderMultiplicity_eq_of_linearEquiv e S

end RingMultiplicity

/-! ### Reconstructing a finite sum from its multiplicities -/

section Reconstruction

variable {R : Type*} [Ring R] [IsSemisimpleRing R]
variable {ι κ : Type*} [Finite ι] [Finite κ]
variable {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
  [∀ i, IsSimpleModule R (N i)]
variable {P : κ → Type*} [∀ j, AddCommGroup (P j)] [∀ j, Module R (P j)]
  [∀ j, IsSimpleModule R (P j)]

/-- **Finite sums of simple modules are determined by their multiplicities.** If two finite
families contain equally many modules in every simple-module isomorphism class, their products are
linearly equivalent. -/
theorem nonempty_linearEquiv_pi_of_natCard_eq
    (h : ∀ c : SimpleSubmoduleClasses R R,
      Nat.card {i // simpleModuleClass R (N i) = c} =
        Nat.card {j // simpleModuleClass R (P j) = c}) :
    Nonempty ((∀ i, N i) ≃ₗ[R] ∀ j, P j) := by
  have efiber : ∀ c, {i // simpleModuleClass R (N i) = c} ≃
      {j // simpleModuleClass R (P j) = c} := fun c ↦ (Finite.card_eq.mp (h c)).some
  let σ : ι ≃ κ := Equiv.ofFiberEquiv efiber
  have hclass (i : ι) : simpleModuleClass R (N i) = simpleModuleClass R (P (σ i)) :=
    (Equiv.ofFiberEquiv_map efiber i).symm
  have hiso (i : ι) : Nonempty (N i ≃ₗ[R] P (σ i)) :=
    simpleModuleClass_eq_iff.mp (hclass i)
  exact ⟨(LinearEquiv.piCongrRight fun i ↦ (hiso i).some).trans
    (LinearEquiv.piCongrLeft R P σ)⟩

end Reconstruction

/-! ### Semisimple modules over an arbitrary ring -/

section ArbitraryRing

universe u v w

variable {R : Type u} [Ring R]

/-- A finitely generated semisimple module is a finite product of quotients of the ring by maximal
left ideals. This is `IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp` with each simple summand
replaced by an isomorphic cyclic module, so that all the factors live in the universe of `R`. -/
theorem IsSemisimpleModule.exists_linearEquiv_pi_quotient (M : Type v) [AddCommGroup M]
    [Module R M] [IsSemisimpleModule R M] [Module.Finite R M] :
    ∃ (n : ℕ) (m : Fin n → Ideal R), (∀ i, (m i).IsMaximal) ∧
      Nonempty (M ≃ₗ[R] ∀ i, R ⧸ m i) := by
  obtain ⟨n, S, e, hS⟩ := IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp R M
  choose m hm e' using fun i ↦ isSimpleModule_iff_quot_maximal.mp (hS i)
  exact ⟨n, m, hm, ⟨e.trans DFinsupp.linearEquivFunOnFintype |>.trans
    (LinearEquiv.piCongrRight fun i ↦ (e' i).some)⟩⟩

/-- **Maps from a finite product of simple modules into a simple module `S`.** Their number is
the number of endomorphisms of `S`, raised to the number of factors isomorphic to `S`: by Schur's
lemma a factor isomorphic to `S` contributes a copy of `End_R(S)`, and any other factor
contributes only the zero map. No base field is involved, and the formula holds even when
`End_R(S)` is infinite, both sides then being `0` or `1` together. -/
theorem natCard_linearMap_pi_eq_pow {ι : Type*} [Finite ι] {N : ι → Type*}
    [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)] [∀ i, IsSimpleModule R (N i)]
    (S : Type w) [AddCommGroup S] [Module R S] [IsSimpleModule R S] :
    Nat.card ((∀ i, N i) →ₗ[R] S) =
      Nat.card (Module.End R S) ^ Nat.card {i // Nonempty (S ≃ₗ[R] N i)} := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  have hval (i : ι) : Nat.card (N i →ₗ[R] S) =
      if Nonempty (S ≃ₗ[R] N i) then Nat.card (Module.End R S) else 1 := by
    split_ifs with h
    · exact Nat.card_congr (h.some.symm.arrowCongrAddEquiv (LinearEquiv.refl R S)).toEquiv
    · have : Subsingleton (N i →ₗ[R] S) :=
        subsingleton_linearMap_of_isEmpty_linearEquiv ⟨fun e ↦ h ⟨e.symm⟩⟩
      exact Nat.card_unique
  rw [Nat.card_congr (LinearMap.lsum R N ℕ).symm.toEquiv, Nat.card_pi,
    Finset.prod_congr rfl fun i _ ↦ hval i, Finset.prod_ite, Finset.prod_const_one, mul_one,
    Finset.prod_const, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]

/-- **Maps from a semisimple module into a simple module count its multiplicity.** For a finitely
generated semisimple module `M` and a simple module `S`,
`#Hom_R(M, S) = #End_R(S) ^ [M : S]`, where `[M : S]` is the Jordan-Hölder multiplicity. When
`End_R(S)` is finite with at least two elements, the number of maps therefore determines the
multiplicity. -/
theorem natCard_linearMap_eq_pow_jordanHolderMultiplicity (M : Type v) [AddCommGroup M]
    [Module R M] [IsSemisimpleModule R M] [Module.Finite R M]
    (S : Type w) [AddCommGroup S] [Module R S] [IsSimpleModule R S] :
    Nat.card (M →ₗ[R] S) = Nat.card (Module.End R S) ^ jordanHolderMultiplicity R M S := by
  obtain ⟨n, m, hm, ⟨e⟩⟩ := IsSemisimpleModule.exists_linearEquiv_pi_quotient (R := R) M
  have (i : Fin n) : IsSimpleModule R (R ⧸ m i) := isSimpleModule_iff_isCoatom.mpr (hm i).out
  rw [Nat.card_congr (e.arrowCongrAddEquiv (LinearEquiv.refl R S)).toEquiv,
    natCard_linearMap_pi_eq_pow, jordanHolderMultiplicity_eq_of_linearEquiv e,
    jordanHolderMultiplicity_pi_eq_natCard]

/-- **Semisimple modules are determined by their Jordan-Hölder multiplicities**, over an arbitrary
ring. Two finitely generated semisimple modules which contain every simple module equally often
are isomorphic. It suffices to test the simple modules in the universe of `R`, since every simple
module is isomorphic to a quotient of `R`.

Over a semisimple ring this is `TauCeti.nonempty_linearEquiv_pi_of_natCard_eq`, where the simple
modules are indexed by the simple left ideals of `R`; in general a simple module need not embed in
`R`, and the factors are matched by isomorphism directly. -/
theorem IsSemisimpleModule.nonempty_linearEquiv_of_jordanHolderMultiplicity_eq
    (M : Type v) (N : Type w) [AddCommGroup M] [Module R M] [IsSemisimpleModule R M]
    [Module.Finite R M] [AddCommGroup N] [Module R N] [IsSemisimpleModule R N]
    [Module.Finite R N]
    (h : ∀ (S : Type u) [AddCommGroup S] [Module R S] [IsSimpleModule R S],
      jordanHolderMultiplicity R M S = jordanHolderMultiplicity R N S) :
    Nonempty (M ≃ₗ[R] N) := by
  obtain ⟨n, a, ha, ⟨eM⟩⟩ := IsSemisimpleModule.exists_linearEquiv_pi_quotient (R := R) M
  obtain ⟨m, b, hb, ⟨eN⟩⟩ := IsSemisimpleModule.exists_linearEquiv_pi_quotient (R := R) N
  -- Index the simple factors of `M` and of `N` together, and group the indices by the isomorphism
  -- class of their factor. The hypothesis says each class has equally many indices on both sides.
  let c : Fin n ⊕ Fin m → Ideal R := Sum.elim a b
  have hc : ∀ x, IsSimpleModule R (R ⧸ c x) := by
    rintro (i | j)
    exacts [isSimpleModule_iff_isCoatom.mpr (ha i).out, isSimpleModule_iff_isCoatom.mpr (hb j).out]
  have (i : Fin n) : IsSimpleModule R (R ⧸ a i) := hc (.inl i)
  have (j : Fin m) : IsSimpleModule R (R ⧸ b j) := hc (.inr j)
  let s : Setoid (Fin n ⊕ Fin m) :=
    { r x y := Nonempty ((R ⧸ c y) ≃ₗ[R] R ⧸ c x)
      iseqv := ⟨fun _ ↦ ⟨LinearEquiv.refl R _⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩,
        fun ⟨e⟩ ⟨e'⟩ ↦ ⟨e'.trans e⟩⟩ }
  have hcount (x : Fin n ⊕ Fin m) :
      Nat.card {i // Quotient.mk s (.inl i) = Quotient.mk s x} =
        Nat.card {j // Quotient.mk s (.inr j) = Quotient.mk s x} := by
    have := hc x
    simp only [Quotient.eq]
    exact ((jordanHolderMultiplicity_eq_of_linearEquiv eM _).trans
      jordanHolderMultiplicity_pi_eq_natCard).symm.trans <| (h (R ⧸ c x)).trans <|
        (jordanHolderMultiplicity_eq_of_linearEquiv eN _).trans
          jordanHolderMultiplicity_pi_eq_natCard
  let e (q : Quotient s) : {i // Quotient.mk s (.inl i) = q} ≃ {j // Quotient.mk s (.inr j) = q} :=
    (Finite.card_eq.mp <| by
      obtain ⟨x, rfl⟩ := Quotient.exists_rep q
      exact hcount x).some
  let σ : Fin n ≃ Fin m := Equiv.ofFiberEquiv e
  have hσ (i : Fin n) : Nonempty ((R ⧸ a i) ≃ₗ[R] R ⧸ b (σ i)) :=
    Quotient.exact (Equiv.ofFiberEquiv_map e i)
  exact ⟨eM.trans <| (LinearEquiv.piCongrRight fun i ↦ (hσ i).some).trans <|
    (LinearEquiv.piCongrLeft R (fun j ↦ R ⧸ b j) σ).trans eN.symm⟩

end ArbitraryRing

/-! ### Reconstructing finite modules from hom-space dimensions -/

section ReconstructionFromHom

variable {k A M P : Type*} [Field k] [Ring A] [Algebra k A]
  [FiniteDimensional k A] [IsSemisimpleRing A]
variable [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M] [Module.Finite A M]
variable [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P] [Module.Finite A P]

/-- **Finite modules over a semisimple algebra are determined by their simple multiplicities.**
If every simple left ideal has hom spaces of the same dimension into `M` and `P`, then `M` and
`P` are linearly equivalent. -/
theorem nonempty_linearEquiv_of_finrank_linearMap_eq
    (h : ∀ (S : Submodule A A) [IsSimpleModule A S],
      Module.finrank k (S →ₗ[A] M) = Module.finrank k (S →ₗ[A] P)) :
    Nonempty (M ≃ₗ[A] P) := by
  obtain ⟨n, SM, eM, hSM⟩ := IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp A M
  obtain ⟨m, SP, eP, hSP⟩ := IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp A P
  let _ (i : Fin n) : IsSimpleModule A (SM i) := hSM i
  let _ (i : Fin m) : IsSimpleModule A (SP i) := hSP i
  let epM : M ≃ₗ[A] ∀ i, SM i := eM.trans DFinsupp.linearEquivFunOnFintype
  let epP : P ≃ₗ[A] ∀ i, SP i := eP.trans DFinsupp.linearEquivFunOnFintype
  have hfiber : ∀ c,
      Nat.card {i // simpleModuleClass A (SM i) = c} =
        Nat.card {j // simpleModuleClass A (SP j) = c} := by
    intro c
    induction c using SimpleSubmoduleClasses.ind with
    | mk S hS =>
      let _ : IsSimpleModule A S := hS
      let _ : Module.Finite k S :=
        Module.Finite.of_injective (S.subtype.restrictScalars k) Subtype.val_injective
      let _ : Module.Finite k (Module.End A S) :=
        .of_injective (LinearMap.restrictScalarsₗ k A S S k) (LinearMap.restrictScalars_injective k)
      have hendpos : 0 < Module.finrank k (Module.End A S) := by
        let _ : Nontrivial S := IsSimpleModule.nontrivial A S
        let _ : Nontrivial (Module.End A S) := inferInstance
        exact Module.finrank_pos
      have hpredM (i : Fin n) : simpleModuleClass A (SM i) =
          SimpleSubmoduleClasses.mk S ↔ Nonempty (S ≃ₗ[A] SM i) := by
        rw [simpleModuleClass_eq_mk_iff]
        exact ⟨fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩⟩
      have hpredP (i : Fin m) : simpleModuleClass A (SP i) =
          SimpleSubmoduleClasses.mk S ↔ Nonempty (S ≃ₗ[A] SP i) := by
        rw [simpleModuleClass_eq_mk_iff]
        exact ⟨fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩⟩
      rw [Nat.card_congr (Equiv.subtypeEquivRight hpredM),
        Nat.card_congr (Equiv.subtypeEquivRight hpredP)]
      apply Nat.eq_of_mul_eq_mul_right hendpos
      rw [← epM.finrank_linearMap_eq_natCard_mul_finrank_end (k := k) (S := S),
        ← epP.finrank_linearMap_eq_natCard_mul_finrank_end (k := k) (S := S), h S]
  exact ⟨epM |>.trans (nonempty_linearEquiv_pi_of_natCard_eq hfiber).some |>.trans epP.symm⟩

end ReconstructionFromHom

/-! ### The isotypic case -/

section Isotypic

variable {k A S : Type*} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [AddCommGroup S] [Module k S] [Module A S] [IsScalarTower k A S] [IsSimpleModule A S]
variable [FiniteDimensional k S]

/-- **The multiplicity of `S` in a power of `S`.**  If `M` is a finite power of the simple module
`S`, the dimension of the space of `A`-linear maps `S → M` is the number of copies.

This is the form Clifford theory uses: an isotypic component of a restriction is a power of a
single constituent, and its multiplicity is read off as a dimension. -/
theorem finrank_linearMap_eq_natCard_of_linearEquiv_pi_const {ι : Type*} [Finite ι] {M : Type*}
    [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M] (e : M ≃ₗ[A] (ι → S)) :
    Module.finrank k (S →ₗ[A] M) = Nat.card ι := by
  rw [finrank_linearMap_eq_natCard_of_linearEquiv_pi (k := k) (S := S) (N := fun _ : ι ↦ S) e]
  exact Nat.card_congr (Equiv.subtypeUnivEquiv fun _ ↦ ⟨LinearEquiv.refl A S⟩)

end Isotypic

/-! ### The isotypic component -/

section IsotypicComponent

variable {k A M S : Type*} [Field k] [Ring A] [Algebra k A]
variable [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
variable [AddCommGroup S] [Module k S] [Module A S] [IsScalarTower k A S] [IsSimpleModule A S]

omit [Module k S] [IsScalarTower k A S] in
/-- **The multiplicity of `S` in `M` is its multiplicity in the `S`-isotypic component**, every
map out of `S` landing there. -/
@[simp]
theorem finrank_linearMap_isotypicComponent :
    Module.finrank k (S →ₗ[A] isotypicComponent A M S) = Module.finrank k (S →ₗ[A] M) :=
  (linearMapIsotypicComponentEquiv k).finrank_eq

variable [IsAlgClosed k] [FiniteDimensional k S] [FiniteDimensional k M]

/-- **The isotypic component is the power of its type with exponent the multiplicity.**  Mathlib's
`IsIsotypicOfType.linearEquiv_fun` writes the component as a finite power of `S`; what is proved
here is that the exponent is the multiplicity `finrank k (S →ₗ[A] M)`, which is the form that
identifies it without reference to the decomposition. -/
theorem nonempty_linearEquiv_isotypicComponent :
    Nonempty (isotypicComponent A M S ≃ₗ[A] (Fin (Module.finrank k (S →ₗ[A] M)) → S)) := by
  have : Module.Finite k ↥(isotypicComponent A M S) :=
    .of_injective ((isotypicComponent A M S).subtype.restrictScalars k) Subtype.val_injective
  have : Module.Finite A ↥(isotypicComponent A M S) :=
    Module.Finite.of_restrictScalars_finite k A _
  obtain ⟨n, ⟨e⟩⟩ := (IsIsotypicOfType.isotypicComponent A M S).linearEquiv_fun
  have hn : Module.finrank k (S →ₗ[A] M) = n := by
    rw [← finrank_linearMap_isotypicComponent (k := k),
      finrank_linearMap_eq_natCard_of_linearEquiv_pi_const (k := k) e]
    simp
  rw [hn]
  exact ⟨e⟩

/-- **The dimension of an isotypic component is the multiplicity times the dimension of its
type.**  This is the counted form of the isotypic decomposition: the `S`-isotypic component of `M`
is `S^{⊕ m}` with `m` the multiplicity `finrank k (S →ₗ[A] M)`. -/
theorem finrank_isotypicComponent :
    Module.finrank k ↥(isotypicComponent A M S)
      = Module.finrank k (S →ₗ[A] M) * Module.finrank k S := by
  obtain ⟨e⟩ := nonempty_linearEquiv_isotypicComponent (k := k) (A := A) (M := M) (S := S)
  rw [(e.restrictScalars k).finrank_eq]
  simp [Module.finrank_pi_fintype]

end IsotypicComponent

/-! ### Positivity for an arbitrary nonzero submodule -/

section Positivity

variable {k A M : Type*} [Field k] [Ring A] [Algebra k A] [AddCommGroup M] [Module k M]
  [Module A M] [IsScalarTower k A M] [FiniteDimensional k M]

/-- **A nonzero submodule has a positive-dimensional hom space.**  The inclusion of a nonzero
`A`-submodule `S` of `M` is a nonzero element of `S →ₗ[A] M`, and that hom space is
finite-dimensional over `k` because `S` and `M` are.  For a simple `S` over a splitting field this
is the statement that a constituent occurs with positive multiplicity.

`A` is a ring rather than a semiring because the finite-dimensionality of the hom space is
`LinearMap.finiteDimensional'`, which needs one; over a semiring `↥S` carries no `AddCommGroup`
instance and `Module.Finite.linearMap` does not apply. -/
theorem finrank_linearMap_pos_of_ne_bot {S : Submodule A M} (hS : S ≠ ⊥) :
    0 < Module.finrank k (S →ₗ[A] M) := by
  have : Module.Finite k ↥S :=
    .of_injective (S.subtype.restrictScalars k) Subtype.val_injective
  obtain ⟨v, hv, hv0⟩ := S.ne_bot_iff.mp hS
  have : Nontrivial (S →ₗ[A] M) :=
    ⟨S.subtype, 0, fun hzero => hv0 (by simpa using DFunLike.congr_fun hzero ⟨v, hv⟩)⟩
  exact Module.finrank_pos

end Positivity

end TauCeti
