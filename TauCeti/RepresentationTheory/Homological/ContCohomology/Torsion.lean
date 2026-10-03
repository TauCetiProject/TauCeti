/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Torsion
public import TauCeti.RepresentationTheory.Continuous.Coinduced
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Additive
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CompactDiscrete
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution

/-!
# Continuous cohomology of a compact group is torsion in positive degrees

Let `G` be a compact group and `X` a topological representation of `G` whose underlying module is
discrete. Every class of `Hⁿ⁺¹(G, X) = continuousCohomology (n + 1) X` is killed by the index of
some open subgroup of `G`, so `Hⁿ⁺¹(G, X)` is a torsion group; and when `X` is a `ℚ`-vector space,
`Hⁿ⁺¹(G, X)` vanishes (NSW (1.6.1)). Degree zero is excluded on purpose: `H⁰(G, X) = X^G` is not
torsion in general, for instance for the trivial action on `ℤ`.

The argument runs on Mathlib's coinduced resolution `X → C(G, X) → C(G, C(G, X)) → ⋯`, whose
differentials are `d₀ = const` and `dₘ₊₁ F = const F - dₘ ∘ F`. Evaluation at any point `x : G`
contracts that resolution, `dₘ (F x) + (dₘ₊₁ F) x = F`, but it is not `G`-equivariant, so it does
not descend to the homogeneous cochains. The sum of the evaluations over a transversal of an open
subgroup `U` does descend, as soon as the cochain `F` is invariant under right translation by `U`.
A homogeneous cochain of a discrete representation of a compact group is locally constant, so its
right-translation stabilizer is such an open subgroup, of finite index `[G : U]`. Summing the
contraction identity over the cosets of `U` then exhibits `[G : U] • F` as a coboundary whenever
`F` is a cocycle of positive degree. For a `ℚ`-vector space `X`, division by `[G : U]` is an
endomorphism of `X`, and the additivity of `Hⁿ⁺¹(G, -)` turns the annihilation into vanishing.

The summed contraction identity is `TopRep.d_sum_apply_add_sum_d_apply`, and the invariance of the
coset sum is `ContRepresentation.sum_apply_out_mem_invariants`.

A second, hypothesis-free form of the same phenomenon is also recorded here: an exponent of the
coefficients is an exponent of `Hⁿ(G, X)` in every degree, for any topological group, by
exponent-inheritance along the coinduced resolution.

## Main results

* `TauCeti.ContinuousCohomology.exists_openSubgroup_index_nsmul_eq_zero`: every class of positive
  degree is killed by the index of an open subgroup.
* `TauCeti.ContinuousCohomology.isAddTorsion_continuousCohomology`: `Hⁿ⁺¹(G, X)` is torsion.
* `TauCeti.ContinuousCohomology.subsingleton_continuousCohomology_of_module_rat`: `Hⁿ⁺¹(G, X)`
  vanishes when `X` is a `ℚ`-vector space.
* `TauCeti.ContinuousCohomology.nsmul_continuousCohomology_eq_zero`: in every degree, and over
  any topological group, `Hⁿ(G, X)` is killed by every `N` that kills `X`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.6.1).
* K. S. Brown, *Cohomology of Groups*, Chapter III, (10.1), the model for finite groups.
-/

public section

open CategoryTheory TopRep

namespace TauCeti.ContinuousCohomology

open _root_.ContinuousCohomology

variable {k G : Type*} [Ring k] [TopologicalSpace k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-! ### Torsion -/

section Torsion

variable [CompactSpace G] {X : TopRep k G} [DiscreteTopology X.V]

/-- **Continuous cohomology of positive degree is killed by finite indices.** Over a compact group,
every class of `Hⁿ⁺¹(G, X)` for a discrete representation `X` is annihilated by the index
`[G : U]` of some open subgroup `U`. -/
theorem exists_openSubgroup_index_nsmul_eq_zero (n : ℕ) (x : continuousCohomology (n + 1) X) :
    ∃ U : OpenSubgroup G, (U : Subgroup G).index • x = 0 := by
  set K := homogeneousCochains X
  obtain ⟨z, rfl⟩ := K.homologyπ_surjective (n + 1) x
  set c := K.iCycles (n + 1) z
  set f : C(G, (resolutionX X (n + 1)).V) := c.1
  -- `f` is locally constant, being a continuous map into a discrete space
  have hf : IsLocallyConstant f := (IsLocallyConstant.iff_continuous f).2 f.continuous
  let U : OpenSubgroup G := ⟨rightTranslationStabilizer f, isOpen_rightTranslationStabilizer hf⟩
  have : Finite (G ⧸ (U : Subgroup G)) := Subgroup.quotient_finite_of_isOpen _ U.isOpen
  let : Fintype (G ⧸ (U : Subgroup G)) := Fintype.ofFinite _
  refine ⟨U, ?_⟩
  -- the cocycle condition `dₙ₊₂ f = 0`
  have hcocycle : (d X (n + 2)).hom f = 0 := by
    have h := ConcreteCategory.congr_hom (K.iCycles_d (n + 1) (n + 2)) z
    simp only [ConcreteCategory.comp_apply] at h
    exact (homogeneousCochains.d_apply X (n + 1) c).symm.trans (congrArg Subtype.val h)
  -- the coset sum of `f` is a homogeneous cochain of degree `n`
  let b : K.X n := ⟨∑ q : G ⧸ (U : Subgroup G), f q.out,
    ContRepresentation.sum_apply_out_mem_invariants c.2 le_rfl⟩
  have hb : K.toCycles n (n + 1) b = (U : Subgroup G).index • z := by
    refine K.iCycles_injective (n + 1) (Subtype.ext ?_)
    have h := ConcreteCategory.congr_hom (K.toCycles_i n (n + 1)) b
    simp only [ConcreteCategory.comp_apply] at h
    rw [h, map_nsmul, homogeneousCochains.d_apply]
    have hsum := d_sum_apply_add_sum_d_apply X (fun q : G ⧸ (U : Subgroup G) => (q.out : G))
      (n + 1) f
    simp only [hcocycle, ContinuousMap.zero_apply, Finset.sum_const_zero, add_zero] at hsum
    rw [Subgroup.index, Nat.card_eq_fintype_card]
    -- `b` is the coset sum of `f` by definition, and the underlying cochain of the multiple of
    -- the cocycle `z` is the same multiple of `f`
    exact hsum
  rw [← map_nsmul, ← hb]
  exact (K.homologyπ_eq_zero_iff (n + 1) (by simp)).2 ⟨b, rfl⟩

/-- **Continuous cohomology of positive degree is torsion** (NSW (1.6.1)). Over a compact group,
`Hⁿ⁺¹(G, X)` is a torsion group for every discrete representation `X`. Degree zero is excluded:
`H⁰(G, X) = X^G` need not be torsion. -/
theorem isAddTorsion_continuousCohomology (n : ℕ) :
    IsAddTorsion (continuousCohomology (n + 1) X) := fun x => by
  obtain ⟨U, hU⟩ := exists_openSubgroup_index_nsmul_eq_zero n x
  exact isOfFinAddOrder_iff_nsmul_eq_zero.2
    ⟨_, Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite), hU⟩

/-- **Continuous cohomology with rational coefficients vanishes in positive degree.** Over a
compact group, `Hⁿ⁺¹(G, X) = 0` for every discrete representation `X` whose underlying group is a
`ℚ`-vector space. -/
theorem subsingleton_continuousCohomology_of_module_rat [Module ℚ X.V] (n : ℕ) :
    Subsingleton (continuousCohomology (n + 1) X) := by
  suffices h : ∀ x : continuousCohomology (n + 1) X, x = 0 from
    ⟨fun x y => (h x).trans (h y).symm⟩
  intro x
  obtain ⟨U, hU⟩ := exists_openSubgroup_index_nsmul_eq_zero n x
  set N := (U : Subgroup G).index
  have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Subgroup.index_ne_zero_of_finite
  -- division by `N` is an endomorphism of `X`, since every additive map is `ℚ`-linear
  let e : X ⟶ X := TopRep.ofHom
    { toFun v := (N : ℚ)⁻¹ • v
      map_add' := smul_add _
      map_smul' c v := (map_rat_smul (smulAddHom k X.V c) _ v).symm
      isIntertwining' g := by ext v; exact (map_rat_smul (X.ρ g) _ v).symm
      cont := continuous_of_discreteTopology }
  have he : N • e = 𝟙 X := by
    ext v
    -- the group structure on morphisms of `TopRep` is transported from the intertwining maps, so
    -- `N • e` acts on `v` as `N • e v` by definition; no `hom_nsmul` lemma is available for it
    change N • ((N : ℚ)⁻¹ • v) = v
    rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, mul_inv_cancel₀ hN, one_smul]
  have hmap : coeffMap (N • e) (n + 1) = N • coeffMap e (n + 1) :=
    (continuousCohomologyFunctor k G (n + 1)).map_nsmul
  rw [he, coeffMap_id] at hmap
  have h := congrArg (fun φ => φ.hom x) hmap
  simp only [TopModuleCat.hom_id, TopModuleCat.hom_nsmul] at h
  simpa [← map_nsmul, hU] using h

end Torsion

/-! ### Exponents inherited from the coefficients -/

section Exponent

variable {X : TopRep k G} {N : ℕ}

/-- Every term of the coinduced resolution of `X` is killed by `N` when `X` is. -/
theorem nsmul_resolutionX_eq_zero (hX : ∀ x : X.V, N • x = 0) :
    ∀ (n : ℕ) (F : (resolutionX X n).V), N • F = 0
  | 0, F => hX F
  -- the `n + 1`-st term is `C(G, (resolutionX X n).V)` by unfolding the coinduction functor, and
  -- its additive structure is pointwise
  | n + 1, F => ContinuousMap.ext fun g ↦ nsmul_resolutionX_eq_zero hX n (F g)

/-- **Continuous cohomology inherits the exponent of its coefficients**: if `N` kills every
element of `X`, then it kills every class of `Hⁿ(G, X)`, in every degree. It is the all-degree
counterpart of `TauCeti.ContCohomology.nsmul_H1_eq_zero` and
`TauCeti.ContCohomology.nsmul_H2_eq_zero`. -/
theorem nsmul_continuousCohomology_eq_zero (hX : ∀ x : X.V, N • x = 0) (n : ℕ)
    (x : continuousCohomology n X) : N • x = 0 := by
  set K := homogeneousCochains X
  obtain ⟨a, rfl⟩ := K.homologyπ_surjective n x
  have ha : N • a = 0 := K.iCycles_injective n <| by
    rw [map_nsmul, _root_.map_zero]
    exact Subtype.ext (nsmul_resolutionX_eq_zero hX (n + 1) _)
  rw [← map_nsmul, ha, _root_.map_zero]

end Exponent

end TauCeti.ContinuousCohomology
