/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Topology.Homology
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Functoriality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution
public import TauCeti.Topology.Algebra.Group.Quotient.Section

import TauCeti.GroupTheory.Coset.Basic

/-!
# Classes killed by restriction to an open subgroup are killed by its index

Let `G` be a locally compact group, for instance a profinite group, `U` an open subgroup of finite
index and `X` a topological representation of `G`. If a class `x ∈ Hⁿ⁺¹(G, X)` restricts to zero
in `Hⁿ⁺¹(U, X)`, then `[G : U] • x = 0`. Classically this is read off from the identity
`cor ∘ res = [G : U]` (NSW (1.5.7)). Applied to an open subgroup of index prime to `p`, and to a
class of `p`-power order, it makes restriction injective. For a profinite group with discrete
`p`-primary torsion coefficients, every cohomology class has `p`-power order; this is how its
cohomology is compared with that of a Sylow subgroup.

The proof uses no corestriction. It works directly on Mathlib's coinduced resolution
`C(G, C(G, …, X))`. The right-coset factorization of an open subgroup provides a continuous map
`w : G → U` with `w (u * g) = u * w g`. Pulling back along `w` in every variable turns a cochain
of `U` into a `U`-invariant cochain of the resolution of `G`. The operators

```text
h₀ = 0,   hₙ₊₁ F x = F (w x) x - hₙ (F (w x)),
```

form a `U`-equivariant homotopy between the identity and "restrict to `U`, then pull back along
`w`". So if the restriction of a `G`-cocycle `F` is the coboundary `d v` of a homogeneous cochain
`v` of `U`, then `F = d W` for the `U`-invariant cochain `W = h F + w^* v`. The coset sum
`∑_{q ∈ G ⧸ U} q.out • W` is then `G`-invariant, and its coboundary is `[G : U] • F`. Local
compactness of `G` is what makes `hₙ₊₁ F` continuous, through the continuity of evaluation.

Degree zero is excluded: there restriction `H⁰(G, X) = X^G → X^U = H⁰(U, X)` is simply injective.

## Main results

* `TauCeti.ContinuousCohomology.index_nsmul_eq_zero_of_res_eq_zero`: a class of `Hⁿ⁺¹(G, X)`
  whose restriction to an open finite-index subgroup `U` vanishes is killed by `[G : U]`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.5.7) and
  (1.6.1).
* K. S. Brown, *Cohomology of Groups*, Chapter III, (9.5) and (10.1).
-/

public section

open CategoryTheory TopRep

namespace TauCeti

universe u v

variable {k : Type u} {G : Type v} [Ring k] [TopologicalSpace k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

namespace ContinuousCohomology

open _root_.ContinuousCohomology

variable (X : TopRep k G) {U : Subgroup G} (w : C(G, U))

/-! ### Pulling cochains of `U` back along a map `G → U` -/

/-- Pullback along `w : G → U` from the coinduced resolution of the restriction of `X` to `U` to
the coinduced resolution of `X`: `F ↦ F ∘ w` in every variable. -/
private noncomputable def resolutionPullback : (n : ℕ) →
    (resolutionX (TopRep.res (U.subtype : U →* G) X) n).V →L[k] (resolutionX X n).V
  | 0 => ContinuousLinearMap.id k X.V
  | n + 1 =>
    { toFun F := (resolutionPullback n : C(_, _)).comp ((F : C(U, _)).comp w)
      map_add' F F' := by ext x; simp
      map_smul' c F := by ext x; simp
      cont := (ContinuousMap.continuous_postcomp _).comp (ContinuousMap.continuous_precomp _) }

private theorem resolutionPullback_zero_apply (v : X.V) : resolutionPullback X w 0 v = v :=
  rfl

private theorem resolutionPullback_succ_apply (n : ℕ)
    (F : (resolutionX (TopRep.res (U.subtype : U →* G) X) (n + 1)).V) (x : G) :
    resolutionPullback X w (n + 1) F x = resolutionPullback X w n (F (w x)) :=
  rfl

/-- Pullback along `w` commutes with the differentials of the two resolutions. -/
private theorem resolutionPullback_d (n : ℕ)
    (v : (resolutionX (TopRep.res (U.subtype : U →* G) X) n).V) :
    resolutionPullback X w (n + 1) ((d (TopRep.res (U.subtype : U →* G) X) n).hom v) =
      (d X n).hom (resolutionPullback X w n v) := by
  induction n with
  | zero =>
    refine ContinuousMap.ext fun x ↦ ?_
    rw [resolutionPullback_succ_apply]
    simp only [d_zero, hom_ofHom, ContRepresentation.coind₁ι_toFun, ContinuousMap.const_apply]
  | succ n ih =>
    refine ContinuousMap.ext fun x ↦ ?_
    rw [resolutionPullback_succ_apply, hom_d_succ_apply_apply, map_sub, ih,
      hom_d_succ_apply_apply, resolutionPullback_succ_apply]

/-- The generic resolution-map equation specialized to restriction, with the representation
identified through `TopRep.res` on the subgroup inclusion. -/
private theorem resolutionMap_subgroupSubtype_succ_apply (n : ℕ) (F : (resolutionX X (n + 1)).V)
    (u : U) :
    (resolutionMap (ContinuousMonoidHom.subgroupSubtype U)
      (𝟙 (TopRep.res (U.subtype : U →* G) X)) (n + 1)).hom F u =
      (resolutionMap (ContinuousMonoidHom.subgroupSubtype U)
        (𝟙 (TopRep.res (U.subtype : U →* G) X)) n).hom (F u) :=
  resolutionMap_succ_apply _ _ n F u

/-! ### The homotopy -/

section Homotopy

variable [LocallyCompactSpace G]

/-- The homotopy `hₙ : C(G, Xₙ) → Xₙ` on the coinduced resolution `Xₙ` of `X`: `h₀ = 0` and
`hₙ₊₁ F x = F (w x) x - hₙ (F (w x))`. It contracts the identity onto restriction to `U` followed
by pullback along `w` (`TauCeti.ContinuousCohomology.d_resolutionHomotopy_add`). -/
private noncomputable def resolutionHomotopy : (n : ℕ) →
    (resolutionX X (n + 1)).V →L[k] (resolutionX X n).V
  | 0 => 0
  | n + 1 =>
    { toFun F := ⟨fun x ↦ F (w x) x - resolutionHomotopy n (F (w x)), by
        have hFw : Continuous fun x : G ↦ (F : C(G, C(G, (resolutionX X n).V))) (w x) :=
          F.continuous.comp (continuous_subtype_val.comp w.continuous)
        exact (hFw.eval continuous_id).sub ((resolutionHomotopy n).continuous.comp hFw)⟩
      map_add' F F' := by ext x; simp; abel
      map_smul' c F := by ext x; simp [smul_sub]
      cont := by
        -- continuity in `F` is joint continuity in `(F, x)`, by evaluation on a locally compact `G`
        refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
        have hFw : Continuous fun p : (resolutionX X (n + 2)).V × G ↦
            (p.1 : C(G, C(G, (resolutionX X n).V))) (w p.2) :=
          continuous_fst.eval (continuous_subtype_val.comp (w.continuous.comp continuous_snd))
        exact (hFw.eval continuous_snd).sub ((resolutionHomotopy n).continuous.comp hFw) }

private theorem resolutionHomotopy_zero : resolutionHomotopy X w 0 = 0 :=
  rfl

private theorem resolutionHomotopy_succ_apply (n : ℕ) (F : (resolutionX X (n + 2)).V) (x : G) :
    resolutionHomotopy X w (n + 1) F x = F (w x) x - resolutionHomotopy X w n (F (w x)) :=
  rfl

/-- Pointwise expansion of the successor homotopy step, before applying the induction hypothesis. -/
private theorem resolutionHomotopy_succ_step (n : ℕ) (F : (resolutionX X (n + 2)).V)
    (x : G) :
    (d X (n + 1)).hom (resolutionHomotopy X w (n + 1) F) x +
        resolutionHomotopy X w (n + 2) ((d X (n + 2)).hom F) x =
      (d X n).hom (resolutionHomotopy X w n (F (w x))) +
        resolutionHomotopy X w (n + 1) ((d X (n + 1)).hom (F (w x))) +
        (F x - F (w x)) := by
  rw [hom_d_succ_apply_apply, resolutionHomotopy_succ_apply,
    resolutionHomotopy_succ_apply, hom_d_succ_apply_apply,
    ContinuousMap.sub_apply, hom_d_succ_apply_apply, map_sub, map_sub]
  abel

/-- Pointwise expansion of the degree-zero homotopy step. -/
private theorem resolutionHomotopy_zero_step (F : (resolutionX X (0 + 1)).V) :
    (d X 0).hom (resolutionHomotopy X w 0 F) +
        resolutionHomotopy X w (0 + 1) ((d X (0 + 1)).hom F) =
      F - resolutionPullback X w (0 + 1)
        ((resolutionMap (ContinuousMonoidHom.subgroupSubtype U)
          (𝟙 (TopRep.res (U.subtype : U →* G) X)) (0 + 1)).hom F) := by
  refine ContinuousMap.ext fun x ↦ ?_
  rw [resolutionHomotopy_zero, zero_apply, map_zero, zero_add,
    resolutionHomotopy_succ_apply, hom_d_succ_apply_apply,
    resolutionHomotopy_zero, zero_apply, sub_zero,
    ContinuousMap.sub_apply, ContinuousMap.sub_apply, resolutionPullback_succ_apply,
    resolutionMap_subgroupSubtype_succ_apply, resolutionPullback_zero_apply]
  simp [d_zero]
  rfl

/-- **The homotopy identity** `d ∘ h + h ∘ d = id - w^* ∘ res_U` on the coinduced resolution. -/
private theorem d_resolutionHomotopy_add (n : ℕ) (F : (resolutionX X (n + 1)).V) :
    (d X n).hom (resolutionHomotopy X w n F) +
        resolutionHomotopy X w (n + 1) ((d X (n + 1)).hom F) =
      F - resolutionPullback X w (n + 1) ((resolutionMap (ContinuousMonoidHom.subgroupSubtype U)
        (𝟙 (TopRep.res (U.subtype : U →* G) X)) (n + 1)).hom F) := by
  induction n with
  | zero =>
    exact resolutionHomotopy_zero_step X w F
  | succ n ih =>
    refine ContinuousMap.ext fun x ↦ ?_
    rw [ContinuousMap.add_apply, ContinuousMap.sub_apply,
      resolutionPullback_succ_apply, resolutionMap_subgroupSubtype_succ_apply]
    rw [resolutionHomotopy_succ_step]
    rw [ih]
    abel

end Homotopy

/-! ### Equivariance for a `U`-equivariant `w` -/

section Equivariance

variable {w} (hw : ∀ (u : U) (g : G), w ((u : G) * g) = u * w g)
include hw

/-- Pullback along a `U`-equivariant `w` is `U`-equivariant. -/
private theorem resolutionPullback_ρ (n : ℕ) (u : U)
    (v : (resolutionX (TopRep.res (U.subtype : U →* G) X) n).V) :
    resolutionPullback X w n ((resolutionX (TopRep.res (U.subtype : U →* G) X) n).ρ u v) =
      (resolutionX X n).ρ u (resolutionPullback X w n v) := by
  induction n with
  -- `U` acts on the restriction of `X` through `G`, by the definition of `TopRep.res`
  | zero => rfl
  | succ n ih =>
    refine ContinuousMap.ext fun x ↦ ?_
    have hwx : w ((u : G)⁻¹ * x) = u⁻¹ * w x := by simpa using hw u⁻¹ x
    rw [resolutionPullback_succ_apply, resolutionX_succ_ρ_apply_apply, ih,
      resolutionX_succ_ρ_apply_apply, resolutionPullback_succ_apply, hwx]

variable [LocallyCompactSpace G]

/-- The homotopy attached to a `U`-equivariant `w` is `U`-equivariant. -/
private theorem resolutionHomotopy_ρ (n : ℕ) (u : U) (F : (resolutionX X (n + 1)).V) :
    resolutionHomotopy X w n ((resolutionX X (n + 1)).ρ u F) =
      (resolutionX X n).ρ u (resolutionHomotopy X w n F) := by
  induction n with
  | zero => simp [resolutionHomotopy_zero]
  | succ n ih =>
    refine ContinuousMap.ext fun x ↦ ?_
    have hwx : (w ((u : G)⁻¹ * x) : G) = (u : G)⁻¹ * w x := by
      simpa using congrArg Subtype.val (hw u⁻¹ x)
    rw [resolutionHomotopy_succ_apply, resolutionX_succ_ρ_apply_apply,
      resolutionX_succ_ρ_apply_apply, ih, resolutionX_succ_ρ_apply_apply,
      resolutionHomotopy_succ_apply, map_sub, hwx]

/-- **A `G`-invariant cocycle whose restriction to `U` is a coboundary is the coboundary of a
`U`-invariant cochain**, given a `U`-equivariant continuous `w : G → U`: if `d F = 0` and the
restriction of `F` to `U` is `d v`, then `F = d W` for `W = h F + w^* v`. -/
private theorem exists_d_eq_of_resolutionMap_subgroupSubtype_eq_d (n : ℕ)
    {F : (resolutionX X (n + 2)).V} (hFinv : F ∈ (resolutionX X (n + 2)).ρ.invariants)
    (hdF : (d X (n + 2)).hom F = 0)
    {v : (resolutionX (TopRep.res (U.subtype : U →* G) X) (n + 1)).V}
    (hvinv : v ∈ (resolutionX (TopRep.res (U.subtype : U →* G) X) (n + 1)).ρ.invariants)
    (hrF : (resolutionMap (ContinuousMonoidHom.subgroupSubtype U)
      (𝟙 (TopRep.res (U.subtype : U →* G) X)) (n + 2)).hom F =
      (d (TopRep.res (U.subtype : U →* G) X) (n + 1)).hom v) :
    ∃ W : (resolutionX X (n + 1)).V,
      (∀ u : U, (resolutionX X (n + 1)).ρ u W = W) ∧ (d X (n + 1)).hom W = F := by
  refine ⟨resolutionHomotopy X w (n + 1) F + resolutionPullback X w (n + 1) v, fun u ↦ ?_, ?_⟩
  · rw [map_add, ← resolutionHomotopy_ρ X hw, ← resolutionPullback_ρ X hw, hFinv u, hvinv u]
  · have h := d_resolutionHomotopy_add X w (n + 1) F
    rw [hdF, map_zero, add_zero, hrF, resolutionPullback_d] at h
    rw [map_add, h, sub_add_cancel]

end Equivariance

/-! ### The coset sum -/

/-- **The coset sum of a `U`-invariant primitive.** If `W` is invariant under a finite-index
subgroup `U` and `d W = F` with `F` invariant under `G`, then the sum of `W` over the transversal
`Quotient.out` of `U` is invariant under `G` and its coboundary is `[G : U] • F`. -/
private theorem sum_out_mem_invariants_and_d_eq [Fintype (G ⧸ U)] (n : ℕ)
    {W : (resolutionX X (n + 1)).V} (hWinv : ∀ u : U, (resolutionX X (n + 1)).ρ u W = W)
    {F : (resolutionX X (n + 2)).V} (hFinv : F ∈ (resolutionX X (n + 2)).ρ.invariants)
    (hW : (d X (n + 1)).hom W = F) :
    ∑ q : G ⧸ U, (resolutionX X (n + 1)).ρ q.out W ∈ (resolutionX X (n + 1)).ρ.invariants ∧
      (d X (n + 1)).hom (∑ q : G ⧸ U, (resolutionX X (n + 1)).ρ q.out W) = U.index • F := by
  refine ⟨fun g ↦ ?_, ?_⟩
  · -- left multiplication by `g` permutes the cosets, and `U`-invariance of `W` absorbs the change
    -- of representatives
    rw [map_sum]
    refine Fintype.sum_bijective (g • ·) (MulAction.bijective g) _ _ fun q ↦ ?_
    obtain ⟨u, hu⟩ : ∃ u : U, g * q.out * u = (g • q).out :=
      ⟨⟨(g * q.out)⁻¹ * (g • q).out, QuotientGroup.eq.mp (QuotientGroup.mk_out_smul g q).symm⟩,
        by simp [mul_assoc]⟩
    rw [← hu, map_mul, map_mul, mul_apply_eq_comp, mul_apply_eq_comp, hWinv u]
  · rw [map_sum, Finset.sum_congr rfl fun q _ ↦ by rw [TopRep.hom_comm_apply, hW, hFinv q.out],
      Finset.sum_const, Finset.card_univ, Subgroup.index, Nat.card_eq_fintype_card]

/-! ### The annihilation theorem -/

variable {X} [LocallyCompactSpace G]

/-- **A class killed by restriction to an open subgroup is killed by the index.** Let `G` be a
locally compact group, for instance a profinite group, and `U` an open subgroup of finite index.
If the restriction to `U` of a class `x ∈ Hⁿ⁺¹(G, X)` vanishes, then `[G : U] • x = 0`. -/
theorem index_nsmul_eq_zero_of_res_eq_zero (hU : IsOpen (U : Set G)) [U.FiniteIndex] {n : ℕ}
    {x : continuousCohomology (n + 1) X} (hx : (res U X (n + 1)).hom x = 0) :
    U.index • x = 0 := by
  obtain ⟨w, -, hwc, -, -, hw, -⟩ := U.exists_continuous_rightCosetFactorization_of_isOpen hU
  set K := homogeneousCochains X
  set KU := homogeneousCochains (TopRep.res (U.subtype : U →* G) X)
  set φ := cochainsMap (ContinuousMonoidHom.subgroupSubtype U)
    (𝟙 (TopRep.res (U.subtype : U →* G) X))
  obtain ⟨z, rfl⟩ := K.homologyπ_surjective (n + 1) x
  -- the restricted cocycle is the coboundary `d v` of a homogeneous cochain `v` of `U`
  have hz : KU.homologyπ (n + 1) (HomologicalComplex.cyclesMap φ (n + 1) z) = 0 := by
    have h := ConcreteCategory.congr_hom (π_map (ContinuousMonoidHom.subgroupSubtype U)
      (𝟙 (TopRep.res (U.subtype : U →* G) X)) (n + 1)) z
    simp only [ConcreteCategory.comp_apply] at h
    rw [res_def] at hx
    exact h.symm.trans hx
  obtain ⟨v, hv⟩ := (KU.homologyπ_eq_zero_iff (n + 1) (m := n) (by simp)).1 hz
  set F := K.iCycles (n + 1) z
  have hdF : (d X (n + 2)).hom F.1 = 0 := by
    have h := ConcreteCategory.congr_hom (K.iCycles_d (n + 1) (n + 2)) z
    simp only [ConcreteCategory.comp_apply] at h
    exact (homogeneousCochains.d_apply X (n + 1) F).symm.trans (congrArg Subtype.val h)
  have hrF : (resolutionMap (ContinuousMonoidHom.subgroupSubtype U)
      (𝟙 (TopRep.res (U.subtype : U →* G) X)) (n + 2)).hom F.1 =
      (d (TopRep.res (U.subtype : U →* G) X) (n + 1)).hom v.1 := by
    have h₁ := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i φ (n + 1)) z
    have h₂ := ConcreteCategory.congr_hom (KU.toCycles_i n (n + 1)) v
    simp only [ConcreteCategory.comp_apply] at h₁ h₂
    rw [hv] at h₂
    exact (congrArg Subtype.val (h₁.symm.trans h₂)).trans (homogeneousCochains.d_apply _ n v)
  -- so `F = d W` for a `U`-invariant `W`, and the coset sum of `W` is a primitive of `[G : U] • F`
  obtain ⟨W, hWinv, hW⟩ := exists_d_eq_of_resolutionMap_subgroupSubtype_eq_d X
    (w := ⟨w, hwc⟩) hw n F.2 hdF v.2 hrF
  let : Fintype (G ⧸ U) := Fintype.ofFinite _
  obtain ⟨hB, hdB⟩ := sum_out_mem_invariants_and_d_eq X n hWinv F.2 hW
  have hb : K.toCycles n (n + 1) ⟨_, hB⟩ = U.index • z := by
    refine K.iCycles_injective (n + 1) (Subtype.ext ?_)
    have h := ConcreteCategory.congr_hom (K.toCycles_i n (n + 1)) ⟨_, hB⟩
    simp only [ConcreteCategory.comp_apply] at h
    rw [h, map_nsmul, homogeneousCochains.d_apply]
    exact hdB
  rw [← map_nsmul, ← hb]
  exact (K.homologyπ_eq_zero_iff (n + 1) (by simp)).2 ⟨_, rfl⟩

end ContinuousCohomology

end TauCeti
