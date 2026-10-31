/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Irreducible
public import TauCeti.LinearAlgebra.CliffordAlgebra.MonomialGroup
public import TauCeti.RepresentationTheory.Spin.LineSign
import TauCeti.Algebra.CentralSimple.End
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import TauCeti.RepresentationTheory.Irreducible
import TauCeti.RepresentationTheory.Spin.Polarization.Exists
import TauCeti.RingTheory.Semisimple.SimpleArtinian

/-!
# The spinor representations of the group of signed monomials

Let `b` be an orthogonal basis of a quadratic space `(V, Q)` whose generators square to `±1`, and
let `G = CliffordAlgebra.monomialGroup Q b` be the finite group of the signed monomials `±e_s`,
with central element `ε = -1`. A representation of `G` in which `ε` acts by `-1` is the same thing
as a module over the Clifford algebra (`CliffordAlgebra.monomialGroupLift`). This file classifies
the irreducible ones through the structure theorem for the Clifford algebra.

Every polarization `P` of `(V, Q)` makes the spinor module `S = ⋀·W` a Clifford module through the
Fock action `TauCeti.spinAction`, and restricting it to `G` gives the representation
`P.monomialGroupRep b`. It is irreducible, and `ε` acts on it by `-1`.

* **Even dimension.** The Fock action is an isomorphism `CliffordAlgebra Q ≃ End S`, so every
  irreducible representation of `G` in which `ε` acts by `-1` is equivalent to
  `P.monomialGroupRep b`. In dimension `2l`, over a separably closed field (where polarizations
  exist), there is therefore exactly one such representation up to equivalence, and it has
  dimension `2 ^ l`.
* **Odd dimension.** The Clifford algebra is `End S × End S`, the two factors being the Fock
  actions of `P` and of the polarization `P⁻ = P.negLineCoordinate` with the opposite line
  coordinate (`TauCeti.SpinPolarizationData.cliffordEquivEndProd`). An irreducible representation
  of `G` in which `ε` acts by `-1` is equivalent to the representation of `P` or to that of `P⁻`,
  according as the central idempotent separating the two factors acts on it by `1` or by `0`. The
  two are inequivalent: the volume element of the basis is a signed monomial, and it acts on them
  by opposite nonzero scalars. So whenever a polarization exists, as it does over a separably
  closed field, there are exactly two such representations up to equivalence; in dimension
  `2l + 1` both have dimension `2 ^ l`.

In every dimension the representations of `P` and of `P⁻` are exchanged by parity: the parity
operator of `⋀·W` is an equivalence between the representation of `P⁻` and that of `P` twisted by
the grade involution `CliffordAlgebra.monomialGroupInvolute`, which sends `±e_s` to
`±(-1) ^ #s e_s`. In odd dimension the parity twist therefore exchanges the two irreducible
representations in which `ε` acts by `-1`.

The classification itself is Morita theory for the simple ring `End S`: a module over it with no
proper nonzero submodule is isomorphic to `S` (`TauCeti.IsIsotypicOfType.of_isSimpleRing`).

## Main definitions

* `TauCeti.SpinPolarizationData.monomialGroupRep`: the representation of the group of signed
  monomials on the spinor module of a polarization.
* `TauCeti.SpinPolarizationData.monomialGroupRepEquivNegLineCoordinate`: the parity operator, as an
  equivalence between the representation of `P⁻` and the parity twist of that of `P`.

## Main results

* `TauCeti.SpinPolarizationData.isIrreducible_monomialGroupRep`: the spinor representation of the
  group of signed monomials is irreducible.
* `TauCeti.SpinPolarizationData.nonempty_equiv_monomialGroupRep_of_even`: in even dimension, every
  irreducible representation in which `ε` acts by `-1` is equivalent to the spinor representation.
* `TauCeti.monomialGroup_nonempty_equiv_of_even` and
  `TauCeti.monomialGroup_finrank_eq_two_pow_of_even`: in dimension `2l`, over a separably closed
  field, there is one such representation up to equivalence, of dimension `2 ^ l`.
* `TauCeti.SpinPolarizationData.nonempty_equiv_monomialGroupRep_or_of_odd`: in odd dimension, every
  irreducible representation in which `ε` acts by `-1` is equivalent to the spinor representation
  of `P` or to that of `P⁻`.
* `TauCeti.SpinPolarizationData.isEmpty_equiv_monomialGroupRep_negLineCoordinate`: in odd dimension
  these two are inequivalent.
* `TauCeti.monomialGroup_finrank_eq_two_pow_of_odd`: in dimension `2l + 1`, over a separably closed
  field, every such representation has dimension `2 ^ l`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), §20.1.
-/

public section

open CliffordAlgebra Module

namespace TauCeti

namespace SpinPolarizationData

/-! ### The spinor representation and its parity twist -/

section CommRing

variable {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q) {I : Type*} (v : I → V)

/-- The representation of the group of signed monomials of a family `v` on the spinor module
`⋀·W` of a polarization `P`: a signed monomial acts through the Fock action of its value. -/
noncomputable def monomialGroupRep :
    Representation K (monomialGroup Q v) (ExteriorAlgebra K P.W) :=
  (spinAction Q P).toRingHom.toMonoidHom.comp
    ((Units.coeHom (CliffordAlgebra Q)).comp (monomialGroup Q v).subtype)

/-- A signed monomial acts on the spinor module through the Fock action of its value. -/
@[simp]
theorem monomialGroupRep_apply (g : monomialGroup Q v) :
    P.monomialGroupRep v g = spinAction Q P ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) :=
  (rfl)

/-- The central element `ε = -1` acts on the spinor module by `-1`. -/
theorem monomialGroupRep_monomialGroupEpsilon :
    P.monomialGroupRep v (monomialGroupEpsilon Q v) = -1 := by
  simp

/-- **The two signs of the line coordinate are exchanged by parity.** The parity operator
`J = involute` of `⋀·W` is an equivalence between the spinor representation of
`P⁻ = P.negLineCoordinate` and that of `P` twisted by the grade involution of the group of signed
monomials. -/
noncomputable def monomialGroupRepEquivNegLineCoordinate :
    (P.negLineCoordinate.monomialGroupRep v).Equiv
      ((P.monomialGroupRep v).comp (monomialGroupInvolute v).toMonoidHom) :=
  .mk (involuteEquiv (Q := (0 : QuadraticForm K P.W))).toLinearEquiv fun g ↦
    LinearMap.ext fun s ↦ by
      simp [P.spinAction_negLineCoordinate_apply]

/-- The parity equivalence `P.monomialGroupRepEquivNegLineCoordinate v` is the grade involution of
`⋀·W`. -/
@[simp]
theorem monomialGroupRepEquivNegLineCoordinate_apply (s : ExteriorAlgebra K P.W) :
    P.monomialGroupRepEquivNegLineCoordinate v s = involute s :=
  (rfl)

end CommRing

/-- **The spinor representation of the group of signed monomials is irreducible** as soon as the
family `v` spans and the squares `Q (v i)` are units: the group then spans the Clifford algebra,
whose Fock action realizes every endomorphism of the spinor module. -/
theorem isIrreducible_monomialGroupRep {F : Type*} [Field F] {V : Type*} [AddCommGroup V]
    [Module F V] {Q : QuadraticForm F V} (P : SpinPolarizationData Q) [FiniteDimensional F P.W]
    {I : Type*} {v : I → V} (hv : Submodule.span F (Set.range v) = ⊤)
    (hQ : ∀ i, IsUnit (Q (v i))) :
    Representation.IsIrreducible (P.monomialGroupRep v) := by
  apply Representation.isIrreducible_of_asAlgebraHom_surjective
  have h : (P.monomialGroupRep v).asAlgebraHom =
      (spinAction Q P).comp (monomialGroupAlgHom Q v) := by
    apply MonoidAlgebra.algHom_ext
    · intro g
      simp
    · ext
  rw [h]
  exact (spinAction_surjective P).comp (monomialGroupAlgHom_surjective v hv hQ)

/-! ### The classification -/

section Classification

variable {F : Type*} [Field F] [Invertible (2 : F)] {V : Type*} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} (P : SpinPolarizationData Q)
  {I : Type*} [LinearOrder I] {b : Basis I F V} {W : Type*} [AddCommGroup W] [Module F W]

omit [FiniteDimensional F V] in
/-- For an irreducible representation in which `ε` acts by `-1`, a subspace invariant under the
corresponding Clifford action is `⊥` or `⊤`. -/
private theorem eq_bot_or_eq_top_of_map_monomialGroupLift_le
    (hb : (QuadraticMap.associated Q).IsOrthoᵢ b) (hQ : ∀ i, Q (b i) = 1 ∨ Q (b i) = -1)
    (ρ : Representation F (monomialGroup Q b) W) [Representation.IsIrreducible ρ]
    (hρ : ρ (monomialGroupEpsilon Q b) = -1) (N : Submodule F W)
    (hN : ∀ x, N.map (monomialGroupLift hb hQ ⟨ρ, hρ⟩ x) ≤ N) : N = ⊥ ∨ N = ⊤ := by
  let σ : Subrepresentation ρ := ⟨N, fun g w hw ↦ by
    rw [← monomialGroupLift_apply_coe hb hQ ⟨ρ, hρ⟩ g]
    exact hN _ ⟨w, hw, rfl⟩⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top σ with h | h
  · exact Or.inl (congrArg Subrepresentation.toSubmodule h)
  · exact Or.inr (congrArg Subrepresentation.toSubmodule h)

/-- An irreducible representation in which `ε` acts by `-1` is equivalent to the spinor
representation of `P` as soon as the kernel of the Fock action of `P` acts on it by zero.

The Clifford action on the representation then factors through the Fock action, that is through
`End S`, and over the simple ring `End S` every module with no proper nonzero submodule is
isomorphic to `S`. -/
private theorem nonempty_equiv_monomialGroupRep_of_ker_le
    (hb : (QuadraticMap.associated Q).IsOrthoᵢ b) (hQ : ∀ i, Q (b i) = 1 ∨ Q (b i) = -1)
    (ρ : Representation F (monomialGroup Q b) W) [hirr : Representation.IsIrreducible ρ]
    (hρ : ρ (monomialGroupEpsilon Q b) = -1)
    (hker : ∀ x, spinAction Q P x = 0 → monomialGroupLift hb hQ ⟨ρ, hρ⟩ x = 0) :
    Nonempty (ρ.Equiv (P.monomialGroupRep b)) := by
  have := hirr.nontrivial
  set φ := monomialGroupLift hb hQ ⟨ρ, hρ⟩
  set S := ExteriorAlgebra F P.W
  -- The Clifford action `φ` on `W` factors through the Fock action, as `ψ : End S → End W`.
  have hc := spinAction_surjective P
  let ψ : Module.End F S →ₐ[F] Module.End F W :=
    (Ideal.Quotient.liftₐ (RingHom.ker (spinAction Q P)) φ fun x hx ↦ hker x hx).comp
      (Ideal.quotientKerAlgEquivOfSurjective hc).symm.toAlgHom
  have hψ (x : CliffordAlgebra Q) : ψ (spinAction Q P x) = φ x := by
    rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      ← Ideal.quotientKerAlgEquivOfSurjective_mk hc, AlgEquiv.symm_apply_apply]
    exact Ideal.Quotient.liftₐ_apply ..
  -- Make `W` a module over `End S` through `ψ`; its action of `f` is, by definition, `ψ f`.
  let _ : Module (Module.End F S) W := Module.compHom W ψ.toRingHom
  have : IsScalarTower F (Module.End F S) W :=
    ⟨fun r f w ↦ by
      change ψ (r • f) w = r • ψ f w
      rw [map_smul, LinearMap.smul_apply]⟩
  have : IsSimpleModule (Module.End F S) W := by
    refine
      { exists_pair_ne := ⟨⊥, ⊤, bot_ne_top⟩
        eq_bot_or_eq_top := fun N ↦ ?_ }
    have hN : ∀ x, (N.restrictScalars F).map (φ x) ≤ N.restrictScalars F := by
      rintro x _ ⟨w, hw, rfl⟩
      rw [← hψ]
      exact N.smul_mem (spinAction Q P x) hw
    rcases eq_bot_or_eq_top_of_map_monomialGroupLift_le hb hQ ρ hρ _ hN with h | h
    · exact Or.inl (by simpa using h)
    · exact Or.inr (by simpa using h)
  -- Over the simple Artinian ring `End S`, the simple module `W` is isomorphic to `S`.
  have : IsArtinianRing (Module.End F S) := IsArtinianRing.of_finite F (Module.End F S)
  have : IsSimpleModule (Module.End F S) (⊤ : Submodule (Module.End F S) W) :=
    IsSimpleModule.congr Submodule.topEquiv
  obtain ⟨e⟩ := IsIsotypicOfType.of_isSimpleRing (Module.End F S) S W ⊤
  let e' : W ≃ₗ[Module.End F S] S := Submodule.topEquiv.symm.trans e
  refine ⟨.mk (e'.restrictScalars F) fun g ↦ LinearMap.ext fun w ↦ ?_⟩
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.restrictScalars_apply, ← monomialGroupLift_apply_coe hb hQ ⟨ρ, hρ⟩ g, ← hψ,
    monomialGroupRep_apply]
  -- The action of `f : End S` on `W` is `ψ f`, so `e'.map_smul` is the intertwining identity.
  exact e'.map_smul _ w

/-- **The irreducible representations with `ε ↦ -1` in even dimension.** For an orthogonal basis
whose generators square to `±1` of a space of even dimension, every irreducible representation of
the group of signed monomials in which `ε` acts by `-1` is equivalent to the spinor representation
of any polarization `P`. -/
theorem nonempty_equiv_monomialGroupRep_of_even
    (hb : (QuadraticMap.associated Q).IsOrthoᵢ b) (hQ : ∀ i, Q (b i) = 1 ∨ Q (b i) = -1)
    (hV : Even (finrank F V)) (ρ : Representation F (monomialGroup Q b) W)
    [Representation.IsIrreducible ρ] (hρ : ρ (monomialGroupEpsilon Q b) = -1) :
    Nonempty (ρ.Equiv (P.monomialGroupRep b)) :=
  P.nonempty_equiv_monomialGroupRep_of_ker_le hb hQ ρ hρ fun x hx ↦ by
    rw [spinAction_injective P hV (hx.trans (map_zero _).symm), map_zero]

/-- **The irreducible representations with `ε ↦ -1` in odd dimension.** For an orthogonal basis
whose generators square to `±1` of a space of odd dimension, every irreducible representation of
the group of signed monomials in which `ε` acts by `-1` is equivalent to the spinor representation
of a polarization `P` or to that of `P⁻ = P.negLineCoordinate`. -/
theorem nonempty_equiv_monomialGroupRep_or_of_odd
    (hb : (QuadraticMap.associated Q).IsOrthoᵢ b) (hQ : ∀ i, Q (b i) = 1 ∨ Q (b i) = -1)
    (hV : Odd (finrank F V)) (ρ : Representation F (monomialGroup Q b) W)
    [Representation.IsIrreducible ρ] (hρ : ρ (monomialGroupEpsilon Q b) = -1) :
    Nonempty (ρ.Equiv (P.monomialGroupRep b)) ∨
      Nonempty (ρ.Equiv (P.negLineCoordinate.monomialGroupRep b)) := by
  have : NeZero (2 : F) := ⟨Invertible.ne_zero 2⟩
  set φ := monomialGroupLift hb hQ ⟨ρ, hρ⟩
  -- A Clifford element is determined by its two Fock actions.
  have hext {x y : CliffordAlgebra Q} (h₁ : spinAction Q P x = spinAction Q P y)
      (h₂ : spinAction Q P.negLineCoordinate x = spinAction Q P.negLineCoordinate y) : x = y :=
    (P.spinAction_prod_bijective hV).1 (Prod.ext h₁ h₂)
  -- The central idempotent `e` acting by `1` through `P` and by `0` through `P⁻`.
  obtain ⟨e, he⟩ := P.spinAction_prod_surjective hV (1, 0)
  simp only [AlgHom.prod_apply, Prod.mk.injEq] at he
  obtain ⟨he₁, he₀⟩ := he
  have hcomm (x : CliffordAlgebra Q) : e * x = x * e := hext (by simp [he₁]) (by simp [he₀])
  have hidem : e * e = e := hext (by simp [he₁]) (by simp [he₀])
  -- The range of `φ e` is invariant, since `e` is central, so it is `⊥` or `⊤`.
  have hrange : ∀ x, (LinearMap.range (φ e)).map (φ x) ≤ LinearMap.range (φ e) := by
    rintro x _ ⟨_, ⟨w, rfl⟩, rfl⟩
    refine ⟨φ x w, ?_⟩
    rw [← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply]
  rcases eq_bot_or_eq_top_of_map_monomialGroupLift_le hb hQ ρ hρ _ hrange with h | h
  · -- `e` acts by `0`, so the kernel of the Fock action of `P⁻` acts by zero.
    have hφe : φ e = 0 := LinearMap.range_eq_bot.mp h
    refine Or.inr (P.negLineCoordinate.nonempty_equiv_monomialGroupRep_of_ker_le hb hQ ρ hρ
      fun x hx ↦ ?_)
    have hx' : x * (1 - e) = 0 := hext (by simp [he₁]) (by simp [hx])
    simpa [mul_sub, hφe] using congrArg φ hx'
  · -- `e` acts by `1`, so the kernel of the Fock action of `P` acts by zero.
    have hφe : φ e = 1 := LinearMap.ext fun w ↦ by
      obtain ⟨w', rfl⟩ := LinearMap.range_eq_top.mp h w
      rw [← Module.End.mul_apply, ← map_mul, hidem, Module.End.one_apply]
    refine Or.inl (P.nonempty_equiv_monomialGroupRep_of_ker_le hb hQ ρ hρ fun x hx ↦ ?_)
    have hx' : x * e = 0 := hext (by simp [hx]) (by simp [he₀])
    simpa [hφe] using congrArg φ hx'

/-- **The two spinor representations are inequivalent in odd dimension.** For an orthogonal basis
whose generators square to `±1` of a space of odd dimension, the spinor representations of the
group of signed monomials attached to `P` and to `P⁻ = P.negLineCoordinate` are not equivalent:
the volume element of the basis is a signed monomial, acting on them by opposite nonzero scalars. -/
theorem isEmpty_equiv_monomialGroupRep_negLineCoordinate
    (hb : (QuadraticMap.associated Q).IsOrthoᵢ b) (hQ : ∀ i, Q (b i) = 1 ∨ Q (b i) = -1)
    (hV : Odd (finrank F V)) :
    IsEmpty ((P.monomialGroupRep b).Equiv (P.negLineCoordinate.monomialGroupRep b)) := by
  refine ⟨fun T ↦ ?_⟩
  have : Fintype I := FiniteDimensional.fintypeBasisIndex b
  -- The volume element of the sorted basis is a signed monomial `g`.
  obtain ⟨g, hg⟩ := exists_monomialGroup_val_eq_basis hb hQ Finset.univ
  rw [basis_eq_prod_map_sort hb] at hg
  -- The sorted basis is an orthogonal spanning list of odd length.
  set l : List I := (Finset.univ : Finset I).sort
  have hl : (l.map b).Pairwise Q.IsOrtho :=
    List.pairwise_map.mpr <| (Finset.univ.sort_nodup _).imp fun hij ↦
      QuadraticMap.associated_isOrtho.mp (hb hij)
  have hlen : Odd (l.map b).length := by
    rwa [List.length_map, Finset.length_sort, Finset.card_univ, ← finrank_eq_card_basis b]
  have hspan : Submodule.span F {x : V | x ∈ l.map b} = ⊤ := by
    have : {x : V | x ∈ l.map b} = Set.range b := by
      ext x
      simp [l]
    rw [this, b.span_eq]
  -- Its volume element acts by `a` through `P` and by `-a` through `P⁻`, with `a ≠ 0`.
  obtain ⟨a, hsq, hP, hN⟩ := P.exists_spinAction_volume_eq_algebraMap hl hlen hspan
  have ha : a ≠ 0 := by
    rintro rfl
    have hQl : ∀ x ∈ l.map b, Q x ≠ 0 := by
      intro x hx
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      rcases hQ i with h | h <;> simp [h]
    exact neg_one_pow_choose_two_mul_prod_map_ne_zero hQl (by rw [← hsq, mul_zero])
  -- So `T` intertwines `a` with `-a`, and then `T 1 = 0`.
  have h1 := congr($(T.isIntertwining' g) 1)
  simp only [LinearMap.comp_apply, Representation.Equiv.coe_toLinearMap, monomialGroupRep_apply,
    hg, hP, hN, Module.algebraMap_end_apply, map_smul, neg_smul] at h1
  have h2 : (2 * a) • T 1 = 0 := by
    rw [mul_smul, two_smul]
    nth_rewrite 1 [h1]
    exact neg_add_cancel _
  have hT : T 1 = 0 := (smul_eq_zero.mp h2).resolve_left (mul_ne_zero (Invertible.ne_zero 2) ha)
  exact one_ne_zero (EquivLike.injective T (hT.trans (map_zero T).symm))

end Classification

end SpinPolarizationData

/-! ### Counting over a separably closed field -/

section SepClosed

variable {F : Type*} [Field F] [IsSepClosed F] [Invertible (2 : F)] {V : Type*} [AddCommGroup V]
  [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V} {I : Type*} [LinearOrder I]
  {b : Basis I F V} {W : Type*} [AddCommGroup W] [Module F W]

/-- **In even dimension there is one irreducible representation with `ε ↦ -1`.** Over a separably
closed field, for an orthogonal basis whose generators square to `±1` of a space of even dimension,
any two irreducible representations of the group of signed monomials in which `ε` acts by `-1`
are equivalent. -/
theorem monomialGroup_nonempty_equiv_of_even
    (hb : (QuadraticMap.associated Q).IsOrthoᵢ b) (hQ : ∀ i, Q (b i) = 1 ∨ Q (b i) = -1)
    (hV : Even (finrank F V)) {W' : Type*} [AddCommGroup W'] [Module F W']
    (ρ : Representation F (monomialGroup Q b) W) [Representation.IsIrreducible ρ]
    (σ : Representation F (monomialGroup Q b) W') [Representation.IsIrreducible σ]
    (hρ : ρ (monomialGroupEpsilon Q b) = -1)
    (hσ : σ (monomialGroupEpsilon Q b) = -1) :
    Nonempty (ρ.Equiv σ) := by
  have : NeZero (2 : F) := ⟨Invertible.ne_zero 2⟩
  let P := SpinPolarizationData.ofNondegenerate Q
    (QuadraticMap.nondegenerate_of_isOrthoᵢ hb fun i ↦ by rcases hQ i with h | h <;> simp [h])
  obtain ⟨e⟩ := P.nonempty_equiv_monomialGroupRep_of_even hb hQ hV ρ hρ
  obtain ⟨e'⟩ := P.nonempty_equiv_monomialGroupRep_of_even hb hQ hV σ hσ
  exact ⟨e.trans e'.symm⟩

/-- **The irreducible representation with `ε ↦ -1` in dimension `2l` has dimension `2 ^ l`**, over
a separably closed field, for an orthogonal basis whose generators square to `±1`. -/
theorem monomialGroup_finrank_eq_two_pow_of_even
    (hb : (QuadraticMap.associated Q).IsOrthoᵢ b) (hQ : ∀ i, Q (b i) = 1 ∨ Q (b i) = -1)
    {l : ℕ} (hV : finrank F V = 2 * l) (ρ : Representation F (monomialGroup Q b) W)
    [Representation.IsIrreducible ρ] (hρ : ρ (monomialGroupEpsilon Q b) = -1) :
    finrank F W = 2 ^ l := by
  have : NeZero (2 : F) := ⟨Invertible.ne_zero 2⟩
  let P := SpinPolarizationData.ofNondegenerate Q
    (QuadraticMap.nondegenerate_of_isOrthoᵢ hb fun i ↦ by rcases hQ i with h | h <;> simp [h])
  obtain ⟨e⟩ := P.nonempty_equiv_monomialGroupRep_of_even hb hQ (hV ▸ even_two_mul l) ρ hρ
  rw [e.toLinearEquiv.finrank_eq, P.finrank_exteriorAlgebra_W_of_finrank_eq_two_mul hV]

/-- **The irreducible representations with `ε ↦ -1` in dimension `2l + 1` have dimension
`2 ^ l`**, over a separably closed field, for an orthogonal basis whose generators square to
`±1`. -/
theorem monomialGroup_finrank_eq_two_pow_of_odd
    (hb : (QuadraticMap.associated Q).IsOrthoᵢ b) (hQ : ∀ i, Q (b i) = 1 ∨ Q (b i) = -1)
    {l : ℕ} (hV : finrank F V = 2 * l + 1) (ρ : Representation F (monomialGroup Q b) W)
    [Representation.IsIrreducible ρ] (hρ : ρ (monomialGroupEpsilon Q b) = -1) :
    finrank F W = 2 ^ l := by
  have : NeZero (2 : F) := ⟨Invertible.ne_zero 2⟩
  let P := SpinPolarizationData.ofNondegenerate Q
    (QuadraticMap.nondegenerate_of_isOrthoᵢ hb fun i ↦ by rcases hQ i with h | h <;> simp [h])
  rw [← P.finrank_exteriorAlgebra_W_of_finrank_eq_two_mul_add_one hV]
  rcases P.nonempty_equiv_monomialGroupRep_or_of_odd hb hQ (hV ▸ odd_two_mul_add_one l) ρ hρ
    with h | h
  · exact h.some.toLinearEquiv.finrank_eq
  · exact h.some.toLinearEquiv.finrank_eq

end SepClosed

end TauCeti
