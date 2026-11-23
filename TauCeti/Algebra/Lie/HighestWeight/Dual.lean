/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Dual
public import TauCeti.Algebra.Lie.HighestWeight.FiniteDimensional
public import TauCeti.Algebra.Lie.HighestWeight.Irreducible
public import TauCeti.Algebra.Lie.HighestWeight.LowestWeight
public import TauCeti.Algebra.Lie.HighestWeight.Verma
public import TauCeti.Algebra.Lie.Multiplicity
public import TauCeti.Algebra.Lie.Weights.Diagonalizable
-- Non-public: these supply the inputs of the proofs, never the vocabulary of a statement.
import TauCeti.Algebra.Lie.HighestWeight.CompleteReducibility
import TauCeti.Algebra.Lie.HighestWeight.Decomposition
import TauCeti.Algebra.Lie.HighestWeight.Existence
import TauCeti.Algebra.Lie.Multiplicity.Dual

/-!
# Duals of highest weight modules and self-duality

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over a field of
characteristic zero, let `H` be a split Cartan subalgebra and `b` a base of its root system, and
let `M` be a finite-dimensional irreducible `L`-module with a highest weight vector of
weight `lam`. This file identifies the highest weight of the dual module `M*` and reads off the
self-duality criterion:

`M` carries a nonzero invariant bilinear form ↔ `M ≃ M*` ↔ `-(w₀ • lam) = lam`,

with `w₀` the longest element of the Weyl group. It then computes the multiplicities of the dual of
an arbitrary finite-dimensional module, and, over an algebraically closed field, reads off the
self-duality criterion for such a module.

## The highest weight of the dual

`TauCeti/Algebra/Lie/HighestWeight/LowestWeight.lean` identifies `w₀ • lam` as the lowest weight of
`M`: nothing lies below it, so subtracting a positive root from it leaves the weight support
(`TauCeti.genWeightSpace_longestElement_smul_sub_root_eq_bot`).

A functional that vanishes on every weight space except the lowest one is then a highest weight
vector of `M*` of weight `-(w₀ • lam)`. Its weight is read off the decomposition of `M` into
weight spaces, and a positive root space kills it because raising a weight into `w₀ • lam` would
have to start below `w₀ • lam`, where `M` is zero.

## The criterion

`M*` is irreducible (`TauCeti.LieModule.isIrreducible_dual`), so the classification of irreducible
highest weight modules by their weight turns the existence of an equivalence `M ≃ M*` into the
equation `-(w₀ • lam) = lam`; and a nonzero invariant bilinear form on `M` is exactly a nonzero
morphism `M → M*`, which by Schur's lemma is an equivalence.

## The criterion at `L(lam)`

At the named carrier `L(lam)` the criterion needs only dominance of `lam`: `L(lam)` is
irreducible with a highest weight vector of weight `lam`, because the Verma module `M(lam)` is
nonzero (`TauCeti.vermaGenerator_ne_zero`), and dominance makes it finite-dimensional.

## Multiplicities in the dual

For dominant integral `lam`, the dual of `L(lam)` is `L(-(w₀ • lam))`. For a finite-dimensional
module `V`, complete reducibility makes the dual of a finite-dimensional irreducible occur in `V*`
as often as the irreducible occurs in `V` (`LieModule.isotypicMultiplicity_dual_dual`). Hence,
writing `m_V(lam)` for the multiplicity of `L(lam)` in `V`,

`m_{V*}(lam) = m_V(-(w₀ • lam))`.

Both sides vanish when `lam` is not dominant integral. Over an algebraically closed field a
finite-dimensional module is determined by its multiplicities
(`TauCeti.nonempty_lieModuleEquiv_iff_forall_isotypicMultiplicity_irreducibleQuotient_eq`), so
`V ≃ V*` exactly when `m_V(lam) = m_V(-(w₀ • lam))` for every dominant integral `lam`.

## Self-duality and the opposition involution

The equation `-(w₀ • lam) = lam` is read on the simple coroots through the opposition involution
`δ` of the base (`TauCeti.neg_longestElement_smul_eq_self_iff`): it says that the coordinates
`lam (αᵢ^∨)` of `lam` are constant on the `δ`-orbits of the simple roots. In particular, when `δ`
fixes every simple root, every finite-dimensional irreducible module is self-dual; conversely, the
fundamental weight `ϖᵢ` gives a module `L(ϖᵢ)` that is self-dual only if `δ` fixes `αᵢ`. So every
`L(lam)` is self-dual exactly when `δ` is trivial.

## Main results

* `TauCeti.exists_isHighestWeightVector_dual`: **the dual module has a highest weight vector of
  weight `-(w₀ • lam)`.**
* `TauCeti.nonempty_lieModuleEquiv_dual_iff` and
  `TauCeti.exists_ne_zero_lieInvariant_iff_neg_longestElement_smul_eq`: **the self-duality
  criterion**, in its module and its bilinear-form form.
* `TauCeti.exists_ne_zero_lieInvariant_irreducibleQuotient_iff`: the same criterion at the named
  carrier `L(lam)`.
* `TauCeti.nonempty_lieModuleEquiv_dual_irreducibleQuotient`: **the dual of `L(lam)` is
  `L(-(w₀ • lam))`**, for dominant integral `lam`.
* `TauCeti.isotypicMultiplicity_dual_irreducibleQuotient`: **the multiplicity of `L(lam)` in `V*`
  is the multiplicity of `L(-(w₀ • lam))` in `V`**, for every finite-dimensional `V` and every
  `lam`.
* `TauCeti.nonempty_lieModuleEquiv_dual_iff_isotypicMultiplicity`: **over an algebraically closed
  field, a finite-dimensional module is self-dual exactly when, for every dominant integral `lam`,
  `L(lam)` and `L(-(w₀ • lam))` occur in it equally often.**
* `TauCeti.nonempty_lieModuleEquiv_dual_iff_forall_opposition`: **self-duality read on the simple
  coroots**, as constancy of `lam (αᵢ^∨)` on the orbits of the opposition involution.
* `TauCeti.nonempty_lieModuleEquiv_dual_of_forall_opposition_eq` and
  `TauCeti.forall_nonempty_lieModuleEquiv_dual_irreducibleQuotient_iff`: every finite-dimensional
  irreducible module is self-dual when the opposition involution is trivial, and every `L(lam)` is
  self-dual only then.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §21.6.
* N. Bourbaki, *Groupes et algèbres de Lie*, Chapitre VIII, §7.5.
-/

public section

namespace TauCeti

open LieAlgebra Module _root_.LieModule

universe u v w

variable {K : Type u} {L : Type v} [Field K] [CharZero K]
  [LieRing L] [LieAlgebra K L] [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

section Irreducible

variable [IsTriangularizable K H L] {b : (IsKilling.rootSystem H).Base} {lam : Dual K H}

variable {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M] {v : M}
  [_root_.LieModule.IsIrreducible K L M]

/-! ### The highest weight vector of the dual -/

variable [FiniteDimensional K M]

/-- **The dual of an irreducible highest weight module has a highest weight vector of weight
`-(w₀ • lam)`.** A functional vanishing on every weight space but the lowest one has weight
`-(w₀ • lam)` because the weight spaces are honest eigenspaces, and a positive root space kills it
because it raises the lowest weight space out of the weight support. -/
theorem exists_isHighestWeightVector_dual (hv : IsHighestWeightVector b lam v) :
    ∃ f : Dual K M,
      IsHighestWeightVector b (-(longestElement (IsKilling.rootSystem H) b • lam)) f := by
  have hlam : IsDominantIntegral b lam := hv.isDominantIntegral
  set w₀ := longestElement (IsKilling.rootSystem H) b
  set mu : Dual K H := w₀ • lam
  -- the lowest weight space is nonzero
  have hmu_ne : genWeightSpace M ⇑mu ≠ ⊥ :=
    genWeightSpace_weylGroup_smul_ne_bot hv hlam w₀ hv.genWeightSpace_ne_bot
  -- the span of the other weight spaces is a proper submodule
  set N : LieSubmodule K H M := genWeightSpaceSpan H M {chi | chi ≠ ⇑mu}
  have hdisj : Disjoint (genWeightSpace M ⇑mu) N :=
    disjoint_genWeightSpace_genWeightSpaceSpan H M (by simp)
  have hNtop : N ≠ ⊤ := fun h => hmu_ne (by simpa [h] using hdisj)
  have hlt : N.toSubmodule < ⊤ := by
    rw [lt_top_iff_ne_top]
    simpa using hNtop
  obtain ⟨f, hf0, hfN⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
  have hfN' : ∀ m ∈ N, f m = 0 := by
    intro m hm
    have hmem : f m ∈ N.toSubmodule.map f := Submodule.mem_map_of_mem hm
    rw [hfN] at hmem
    simpa using hmem
  -- `f` kills every weight space other than the lowest one
  have hkill : ∀ chi : H → K, chi ≠ ⇑mu → ∀ m ∈ genWeightSpace M chi, f m = 0 :=
    fun _ hchi _ hm => hfN' _ (genWeightSpace_le_genWeightSpaceSpan hchi hm)
  refine ⟨f, isHighestWeightVector_of_forall_rootSpace hf0 (fun x => ?_) (fun alpha ha x hx => ?_)⟩
  · -- the Cartan subalgebra acts through `-mu`
    refine sub_eq_zero.mp (eq_zero_of_forall_genWeightSpace (L := H) fun chi m hm => ?_)
    have hlie : ⁅(x : L), m⁆ = chi x • m := mem_genWeightSpace_iff_forall_lie_eq_smul.mp hm x
    rcases eq_or_ne chi ⇑mu with rfl | hchi
    · simp [Module.Dual.lie_apply, hlie]
    · simp [Module.Dual.lie_apply, hlie, hkill chi hchi m hm]
  · -- a positive root space kills `f`
    refine eq_zero_of_forall_genWeightSpace (L := H) fun chi m hm => ?_
    rw [Module.Dual.lie_apply, neg_eq_zero]
    rcases eq_or_ne ((alpha : H → K) + chi) ⇑mu with hsum | hsum
    · -- the raised weight is the lowest one, so `m` lives below it and is zero
      have hchi : chi = ⇑mu - (alpha : H → K) := eq_sub_of_add_eq' hsum
      rw [hchi] at hm
      rw [genWeightSpace_longestElement_smul_sub_root_eq_bot hv hlam ha] at hm
      rw [(_root_.LieSubmodule.mem_bot _).mp hm]
      simp
    · exact hkill _ hsum _ (lie_mem_genWeightSpace_of_mem_genWeightSpace hx hm)

/-! ### The self-duality criterion -/

/-- **A finite-dimensional irreducible module is self-dual exactly when `-(w₀ • lam) = lam`.** The
dual is irreducible with highest weight `-(w₀ • lam)`, and irreducible highest weight modules are
classified by their weight. -/
theorem nonempty_lieModuleEquiv_dual_iff (hv : IsHighestWeightVector b lam v) :
    Nonempty (M ≃ₗ⁅K,L⁆ Dual K M) ↔
      -(longestElement (IsKilling.rootSystem H) b • lam) = lam := by
  obtain ⟨f, hf⟩ := exists_isHighestWeightVector_dual hv
  have _i := TauCeti.LieModule.isIrreducible_dual (K := K) (L := L) (M := M)
  exact (nonempty_lieModuleEquiv_iff_eq_of_isHighestWeightVector hv hf).trans eq_comm

/-- **The self-duality criterion in its invariant-form shape.** A finite-dimensional irreducible
module with highest weight `lam` carries a nonzero invariant bilinear form exactly when
`-(w₀ • lam) = lam`.

`TauCeti.IsDominantIntegral.neg_longestElement_smul` records the pointwise reading of `w₀` behind
this: whenever `lam` is dominant integral, so is `-(w₀ • lam)`, that is, `w₀ • lam` lands in the
negative of the dominant integral weights. -/
theorem exists_ne_zero_lieInvariant_iff_neg_longestElement_smul_eq
    (hv : IsHighestWeightVector b lam v) :
    (∃ Φ : LinearMap.BilinForm K M, Φ ≠ 0 ∧ Φ.lieInvariant L) ↔
      -(longestElement (IsKilling.rootSystem H) b • lam) = lam :=
  TauCeti.LieModule.exists_ne_zero_lieInvariant_iff_nonempty_lieModuleEquiv_dual.trans
    (nonempty_lieModuleEquiv_dual_iff hv)

/-- **The self-duality criterion at the named carrier `L(lam)`.** For dominant integral `lam`,
the module `L(lam)` carries a nonzero invariant bilinear form exactly when `-(w₀ • lam) = lam`.

Dominance makes `L(lam)` finite-dimensional
(`TauCeti.finiteDimensional_of_isHighestWeightVector_of_isDominantIntegral`), so no
finite-dimensionality hypothesis is needed. -/
theorem exists_ne_zero_lieInvariant_irreducibleQuotient_iff (hlam : IsDominantIntegral b lam) :
    (∃ Φ : LinearMap.BilinForm K (irreducibleQuotient b lam), Φ ≠ 0 ∧ Φ.lieInvariant L) ↔
      -(longestElement (IsKilling.rootSystem H) b • lam) = lam := by
  have hgen := isHighestWeightVector_irreducibleQuotientGenerator b lam
  have _j := finiteDimensional_of_isHighestWeightVector_of_isDominantIntegral hgen hlam
  exact exists_ne_zero_lieInvariant_iff_neg_longestElement_smul_eq hgen

/-! ### The dual of `L(lam)` -/

variable (b) in
/-- **The dual of `L(lam)` is `L(-(w₀ • lam))`**, for dominant integral `lam`. -/
theorem nonempty_lieModuleEquiv_dual_irreducibleQuotient (hlam : IsDominantIntegral b lam) :
    Nonempty (Dual K (irreducibleQuotient b lam) ≃ₗ⁅K,L⁆
      irreducibleQuotient b (-(longestElement (IsKilling.rootSystem H) b • lam))) := by
  have hgen := isHighestWeightVector_irreducibleQuotientGenerator b lam
  have _i := finiteDimensional_of_isHighestWeightVector_of_isDominantIntegral hgen hlam
  have _j := TauCeti.LieModule.isIrreducible_dual (K := K) (L := L)
    (M := irreducibleQuotient b lam)
  obtain ⟨f, hf⟩ := exists_isHighestWeightVector_dual hgen
  exact (nonempty_lieModuleEquiv_iff_eq_of_isHighestWeightVector hf
    (isHighestWeightVector_irreducibleQuotientGenerator b _)).mpr rfl

/-! ### Self-duality and the opposition involution -/

/-- **Self-duality read on the simple coroots.** A finite-dimensional irreducible module with
highest weight `lam` is self-dual exactly when the values of `lam` on the simple coroots are
constant on the orbits of the opposition involution `δ = -w₀`: `lam (α_{δ i}^∨) = lam (αᵢ^∨)` for
every simple root `αᵢ`. -/
theorem nonempty_lieModuleEquiv_dual_iff_forall_opposition (hv : IsHighestWeightVector b lam v) :
    Nonempty (M ≃ₗ⁅K,L⁆ Dual K M) ↔ ∀ i ∈ b.support,
      lam ((IsKilling.rootSystem H).coroot (opposition (IsKilling.rootSystem H) b i)) =
        lam ((IsKilling.rootSystem H).coroot i) := by
  rw [nonempty_lieModuleEquiv_dual_iff hv,
    neg_longestElement_smul_eq_self_iff RootPairing.IsRootSystem.span_coroot_eq_top]
  simp only [rootSystem_coroot'_apply]

/-- **If the opposition involution fixes every simple root, every finite-dimensional irreducible
module is self-dual**, over an algebraically closed field. -/
theorem nonempty_lieModuleEquiv_dual_of_forall_opposition_eq [IsAlgClosed K]
    (h : ∀ i ∈ b.support, opposition (IsKilling.rootSystem H) b i = i) :
    Nonempty (M ≃ₗ⁅K,L⁆ Dual K M) := by
  -- The module has a highest weight vector, and its weight satisfies the coroot criterion.
  obtain ⟨lam, v, hv, -⟩ := exists_isHighestWeightVector_and_lieSpan_eq_top (M := M) b
  exact (nonempty_lieModuleEquiv_dual_iff_forall_opposition hv).mpr fun i hi ↦ by rw [h i hi]

/-- **Every `L(lam)`, for `lam` dominant integral, is self-dual exactly when the opposition
involution fixes every simple root.** -/
theorem forall_nonempty_lieModuleEquiv_dual_irreducibleQuotient_iff :
    (∀ lam : Dual K H, IsDominantIntegral b lam →
      Nonempty (irreducibleQuotient b lam ≃ₗ⁅K,L⁆ Dual K (irreducibleQuotient b lam))) ↔
      ∀ i ∈ b.support, opposition (IsKilling.rootSystem H) b i = i := by
  classical
  refine ⟨fun h i hi ↦ ?_, fun h lam hlam ↦ ?_⟩
  · -- The fundamental weight `ϖᵢ`, with `ϖᵢ (αⱼ^∨) = δᵢⱼ` on the simple coroots, is dominant
    -- integral, and `L(ϖᵢ)` is self-dual only if `δ i = i`.
    let ϖ := b.toCoweightBasis.dualBasis ⟨i, hi⟩
    have hϖ (j : b.support) :
        ϖ ((IsKilling.rootSystem H).coroot j) = if j = ⟨i, hi⟩ then 1 else 0 := by
      rw [← RootPairing.Base.toCoweightBasis_apply, Basis.dualBasis_apply_self]
    have hdom : IsDominantIntegral b ϖ := isDominantIntegral_iff.mpr fun j hj ↦
      ⟨if (⟨j, hj⟩ : b.support) = ⟨i, hi⟩ then 1 else 0, by rw [hϖ ⟨j, hj⟩]; split_ifs <;> simp⟩
    have hgen := isHighestWeightVector_irreducibleQuotientGenerator b ϖ
    have _j := finiteDimensional_of_isHighestWeightVector_of_isDominantIntegral hgen hdom
    have hopp := (nonempty_lieModuleEquiv_dual_iff_forall_opposition hgen).mp (h ϖ hdom) i hi
    have hmem := opposition_mem_support (IsKilling.rootSystem H) b hi
    rw [hϖ ⟨_, hmem⟩, hϖ ⟨i, hi⟩] at hopp
    by_contra hne
    simp [hne] at hopp
  · have hgen := isHighestWeightVector_irreducibleQuotientGenerator b lam
    have _j := finiteDimensional_of_isHighestWeightVector_of_isDominantIntegral hgen hlam
    exact (nonempty_lieModuleEquiv_dual_iff_forall_opposition hgen).mpr fun i hi ↦ by rw [h i hi]

end Irreducible

/-! ### Multiplicities in the dual of an arbitrary module -/

variable {V : Type w} [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
  [FiniteDimensional K V]

section Multiplicity

variable [IsTriangularizable K H L] {b : (IsKilling.rootSystem H).Base}

variable (b) in
/-- **The multiplicity of `L(lam)` in the dual `V*` is the multiplicity of `L(-(w₀ • lam))` in
`V`**, for every finite-dimensional module `V` and every weight `lam`. -/
theorem isotypicMultiplicity_dual_irreducibleQuotient (lam : Dual K H) :
    LieModule.isotypicMultiplicity K L (Dual K V) (irreducibleQuotient b lam) =
      LieModule.isotypicMultiplicity K L V
        (irreducibleQuotient b (-(longestElement (IsKilling.rootSystem H) b • lam))) := by
  set mu := -(longestElement (IsKilling.rootSystem H) b • lam)
  have hmu' : -(longestElement (IsKilling.rootSystem H) b • mu) = lam := by
    rw [smul_neg, smul_smul_longestElement, neg_neg]
  by_cases hlam : IsDominantIntegral b lam
  swap
  · -- Neither `L(lam)` nor `L(mu)` is finite-dimensional, so neither occurs.
    have hmu : ¬ IsDominantIntegral b mu := fun hmu ↦ hlam (hmu' ▸ hmu.neg_longestElement_smul)
    have hfin : ∀ nu : Dual K H, ¬ IsDominantIntegral b nu →
        ¬ Module.Finite K (irreducibleQuotient b nu) := fun nu hnu hfin ↦
      hnu ((finiteDimensional_iff_isDominantIntegral_of_isHighestWeightVector
        (isHighestWeightVector_irreducibleQuotientGenerator b nu)).mp hfin)
    rw [LieModule.isotypicMultiplicity_eq_zero_of_not_finite _ _ _ _ (hfin lam hlam),
      LieModule.isotypicMultiplicity_eq_zero_of_not_finite _ _ _ _ (hfin mu hmu)]
  have hmu : IsDominantIntegral b mu := hlam.neg_longestElement_smul
  have _i := finiteDimensional_irreducibleQuotient_of_isDominantIntegral hmu
  have _j := complementedLattice_lieSubmodule_of_isKilling K L V
  obtain ⟨e⟩ := nonempty_lieModuleEquiv_dual_irreducibleQuotient b hmu
  rw [hmu'] at e
  rw [← LieModule.isotypicMultiplicity_eq_of_lieModuleEquiv_type e,
    LieModule.isotypicMultiplicity_dual_dual]

end Multiplicity

section SelfDual

variable [IsAlgClosed K] {b : (IsKilling.rootSystem H).Base}

variable (b) in
/-- **The self-duality criterion for an arbitrary finite-dimensional module.** Over an
algebraically closed field, a finite-dimensional module `V` is equivalent to its dual exactly when,
for every dominant integral `lam`, the modules `L(lam)` and `L(-(w₀ • lam))` occur in `V` equally
often. -/
theorem nonempty_lieModuleEquiv_dual_iff_isotypicMultiplicity :
    Nonempty (V ≃ₗ⁅K,L⁆ Dual K V) ↔ ∀ lam : Dual K H, IsDominantIntegral b lam →
      LieModule.isotypicMultiplicity K L V (irreducibleQuotient b lam) =
        LieModule.isotypicMultiplicity K L V
          (irreducibleQuotient b (-(longestElement (IsKilling.rootSystem H) b • lam))) := by
  rw [nonempty_lieModuleEquiv_iff_forall_isotypicMultiplicity_irreducibleQuotient_eq b]
  simp_rw [isotypicMultiplicity_dual_irreducibleQuotient b]

end SelfDual

end TauCeti
