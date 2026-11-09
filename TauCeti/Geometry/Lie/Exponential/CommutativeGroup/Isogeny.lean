/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Exponential.CommutativeGroup.Character
public import TauCeti.Geometry.Lie.Exponential.LocalInverse
public import TauCeti.Analysis.Matrix.UnitaryGroup.Torus
public import Mathlib.GroupTheory.Index

/-!
# Period lattices under isogenies

Let `f : G → G'` be a continuous homomorphism of finite-dimensional real Lie groups whose Lie map
`df : 𝔤 → 𝔤'` is a linear isomorphism, for instance a surjective homomorphism with finite kernel
between groups of the same dimension (an *isogeny*). Then `df` carries the period lattice
`Λ_ℤ(G) = (2π)⁻¹ ker(exp)` into `Λ_ℤ(G')` (`ContinuousMonoidHom.lieMap_mem_periodLattice`), but in
general not onto it: for commutative `G` and `G'` with `G` connected, the image has index the order
of the kernel of `f`,

`[Λ_ℤ(G') : df(Λ_ℤ(G))] = |ker f|`

(`ContinuousMonoidHom.relIndex_map_lieMap_periodLattice`). Indeed, `Y ↦ exp(df⁻¹(2π Y))` maps
`Λ_ℤ(G')` onto `ker f`, since every element of the connected group `G` is an exponential, and its
kernel is exactly `df(Λ_ℤ(G))`.

The hypothesis on `df` is met by isogenies: if `ker f` is discrete then `df` is injective
(`ContinuousMonoidHom.lieMap_injective_of_discreteTopology_ker`), because for `df X = 0` the
one-parameter subgroup `t ↦ exp(t X)` is a connected subset of `ker f` through `1`, so it is
trivial and `X = 0`.

The standard example is the central isogeny of `U(2)`. Its diagonal torus `T ≅ S¹ × S¹`,
`diag(z₁, z₂) ↦ (z₁, z₂)` (`TauCeti.unitaryTorusHom`), contains the identity component of the
centre `Z = {diag(a, a)}` and the torus `T_ss = {diag(b, b⁻¹)}` of `SU(2)`. Their product map
`Z × T_ss → T` is `(a, b) ↦ (a b, a b⁻¹)` (`TauCeti.unitaryTorusCentralIsogeny`,
`TauCeti.unitaryTorusHom_unitaryTorusCentralIsogeny`), whose kernel is
`{(1, 1), (-1, -1)}`. So the real splitting `𝔱 = 𝔷 ⊕ 𝔱_ss` of the Lie algebra does not split the
period lattice of `T` integrally: `Λ_ℤ(Z) ⊕ Λ_ℤ(T_ss)` has index two in `Λ_ℤ(T)`
(`TauCeti.relIndex_map_lieMap_unitaryTorusCentralIsogeny_periodLattice`).

## Main results

* `ContinuousMonoidHom.lieMap_injective_of_discreteTopology_ker`: a continuous homomorphism with
  discrete kernel has injective Lie map.
* `ContinuousMonoidHom.relIndex_map_lieMap_periodLattice`: for commutative groups with connected
  source and bijective Lie map, the image of the period lattice of the source has index the order
  of the kernel in the period lattice of the target.
* `TauCeti.card_ker_unitaryTorusCentralIsogeny`,
  `TauCeti.relIndex_map_lieMap_unitaryTorusCentralIsogeny_periodLattice`: the central isogeny
  `(a, b) ↦ (a b, a b⁻¹)` of the torus of `U(2)` has kernel of order two, and the period lattice of
  its source has index two in that of its target.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter I, § 3 (The Exponential Map).
* D. Bump, *Lie Groups*, 2nd ed., Springer GTM 225 (2013), Chapter 15 (Tori).
-/

public section

noncomputable section

open Filter Real
open scoped ContDiff Manifold Topology

namespace ContinuousMonoidHom

open TauCeti

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [Group G']
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [LieGroup I ∞ G] [LieGroup I' ∞ G']

/-- **A continuous homomorphism with discrete kernel has injective Lie map.** In particular the Lie
map of a homomorphism with finite kernel is injective. -/
theorem lieMap_injective_of_discreteTopology_ker (f : G →ₜ* G') [DiscreteTopology f.ker] :
    Function.Injective (lieMap (I := I) (I' := I') f) := by
  refine (injective_iff_map_eq_zero (lieMap (I := I) (I' := I') f).toLinearMap).2 fun X hX ↦ ?_
  have hX' : lieMap (I := I) (I' := I') f X = 0 := hX
  -- The exponentials of `G` and `G'` need these instances; they hold for every Lie group.
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have : BoundarylessManifold I G := ContMDiffMul.boundarylessManifold
  have : T2Space G' := I'.t2Space_of_lieGroup ∞
  have : BoundarylessManifold I' G' := ContMDiffMul.boundarylessManifold
  -- The one-parameter subgroup through `X`, as a continuous curve in the kernel of `f`.
  have hcont : Continuous fun t : ℝ ↦ lieExp (I := I) (G := G) (t • X) :=
    (contMDiff_lieExp (I := I) (G := G)).continuous.comp (continuous_id.smul continuous_const)
  have hker (t : ℝ) : lieExp (I := I) (G := G) (t • X) ∈ f.ker := by
    rw [MonoidHom.mem_ker, ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_ofClass,
      map_lieExp (I' := I'), map_smul, hX', smul_zero, lieExp_zero]
  have hone (t : ℝ) : lieExp (I := I) (G := G) (t • X) = 1 := by
    -- A continuous curve in a discrete subgroup is constant.
    have hc : Continuous fun t : ℝ ↦ (⟨_, hker t⟩ : f.ker) := hcont.subtype_mk hker
    have h := PreconnectedSpace.constant inferInstance hc (x := t) (y := 0)
    simpa [lieExp_zero] using congrArg Subtype.val h
  -- Near `0` the Lie logarithm inverts the exponential, so `t • X = 0` for small `t ≠ 0`.
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ≠ 0 ∧ t • X = 0 := by
    have hlim : Tendsto (fun t : ℝ ↦ t • X) (𝓝 0) (𝓝 0) :=
      (continuous_id.smul continuous_const).tendsto' (0 : ℝ) 0 (by simp)
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (hlim.eventually (eventually_lieLog_lieExp (I := I) (G := G)))]
      with t ht hlog
    rw [hone t, lieLog_one] at hlog
    exact ⟨ht, hlog.symm⟩
  obtain ⟨t, ht, htX⟩ := hev.exists
  exact (smul_eq_zero.1 htX).resolve_left ht

variable [T2Space G] [BoundarylessManifold I G] [T2Space G'] [BoundarylessManifold I' G']
  [IsMulCommutative G] [IsMulCommutative G'] [IsTopologicalGroup G] [PreconnectedSpace G]

/-- **The index of the period lattice under an isogeny.** Let `f : G → G'` be a continuous
homomorphism of commutative Lie groups, with `G` connected, whose Lie map `df` is bijective. Then
the image `df(Λ_ℤ(G))` of the period lattice of `G` has index `|ker f|` in the period lattice of
`G'`. In particular it has finite index exactly when `ker f` is finite. -/
theorem relIndex_map_lieMap_periodLattice (f : G →ₜ* G')
    (hf : Function.Bijective (lieMap (I := I) (I' := I') f)) :
    ((periodLattice I G).map (lieMap (I := I) (I' := I') f).toLinearMap.toAddMonoidHom).relIndex
        (periodLattice I' G') = Nat.card f.ker := by
  set e := LinearEquiv.ofBijective (lieMap (I := I) (I' := I') f).toLinearMap hf
  have he (X : LeftInvariantDerivation I G) : e X = lieMap (I := I) (I' := I') f X :=
    LinearEquiv.ofBijective_apply _ _
  -- `ψ Y = exp(df⁻¹(2π Y))`, an additive homomorphism because `G` is commutative.
  let ψ : LeftInvariantDerivation I' G' →+ Additive G :=
    (lieExpAddMonoidHom (I := I) (G := G)).comp
      ((e.symm.toLinearMap.comp ((2 * π) • LinearMap.id)).toAddMonoidHom)
  have hψ (Y : LeftInvariantDerivation I' G') :
      ψ Y = Additive.ofMul (lieExp (I := I) (G := G) (e.symm ((2 * π) • Y))) :=
    lieExpAddMonoidHom_apply _
  -- The kernel of `ψ` is the image of the period lattice of `G`.
  have hkerψ : ψ.ker =
      (periodLattice I G).map (lieMap (I := I) (I' := I') f).toLinearMap.toAddMonoidHom := by
    ext Y
    rw [AddMonoidHom.mem_ker, hψ, ofMul_eq_zero, AddSubgroup.mem_map]
    constructor
    · intro hY
      refine ⟨e.symm Y, ?_, by simp [← he]⟩
      rwa [mem_periodLattice, ← map_smul]
    · rintro ⟨X, hX, rfl⟩
      rw [mem_periodLattice] at hX
      simpa [← he, ← map_smul] using hX
  -- The image under `ψ` of the period lattice of `G'` is the kernel of `f`.
  have hmap : (periodLattice I' G').map ψ = f.ker.toAddSubgroup := by
    ext g
    rw [AddSubgroup.mem_map, Additive.mem_toAddSubgroup, MonoidHom.mem_ker,
      ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_ofClass]
    constructor
    · rintro ⟨Y, hY, rfl⟩
      rw [mem_periodLattice] at hY
      rw [hψ, toMul_ofMul, map_lieExp (I' := I'), ← he, e.apply_symm_apply, hY]
    · intro hg
      obtain ⟨X, hX⟩ := lieExp_surjective_of_preconnectedSpace (I := I) (G := G) (Additive.toMul g)
      refine ⟨(2 * π)⁻¹ • e X, ?_, ?_⟩
      · rw [mem_periodLattice, smul_inv_smul₀ two_pi_pos.ne', he, ← map_lieExp (I' := I'), hX, hg]
      · rw [hψ, smul_inv_smul₀ two_pi_pos.ne', e.symm_apply_apply, hX, ofMul_toMul]
  rw [← hkerψ, AddSubgroup.relIndex_ker, hmap]
  exact Nat.card_congr (Additive.toMul.subtypeEquiv fun g ↦ Additive.mem_toAddSubgroup _ g)

end ContinuousMonoidHom

namespace TauCeti

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- The **central isogeny of the torus of `U(2)`**, `(a, b) ↦ (a b, a b⁻¹)`. In the coordinates
`diag(z₁, z₂) ↦ (z₁, z₂)` of the diagonal torus `T` of `U(2)`, it is the multiplication map
`Z × T_ss → T` from the product of the identity component `Z = {diag(a, a)}` of the centre and
the torus `T_ss = {diag(b, b⁻¹)}` of `SU(2)`. -/
def unitaryTorusCentralIsogeny : Circle × Circle →ₜ* Circle × Circle :=
  (ContinuousMonoidHom.mul Circle).prod
    ((ContinuousMonoidHom.mul Circle).comp
      ((ContinuousMonoidHom.id Circle).prodMap (ContinuousMonoidHom.inv Circle)))

@[simp]
theorem unitaryTorusCentralIsogeny_apply (p : Circle × Circle) :
    unitaryTorusCentralIsogeny p = (p.1 * p.2, p.1 * p.2⁻¹) :=
  (rfl)

/-- **The central isogeny inside `U(2)`.** The diagonal matrix `diag(a b, a b⁻¹)` of the image of
`(a, b)` is the product of `diag(a, a)` and `diag(b, b⁻¹)`. -/
theorem unitaryTorusHom_unitaryTorusCentralIsogeny (a b : Circle) :
    unitaryTorusHom (Fin 2)
        ![(unitaryTorusCentralIsogeny (a, b)).1, (unitaryTorusCentralIsogeny (a, b)).2] =
      unitaryTorusHom (Fin 2) ![a, a] * unitaryTorusHom (Fin 2) ![b, b⁻¹] := by
  rw [← map_mul]
  congr 1
  ext i
  fin_cases i <;> simp

/-- The first factor `diag(a, a)` is the scalar matrix `a • 1`, so it lies in the centre of
`U(2)`. -/
theorem coe_unitaryTorusHom_const (a : Circle) :
    (unitaryTorusHom (Fin 2) ![a, a] : Matrix (Fin 2) (Fin 2) ℂ) = (a : ℂ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The second factor `diag(b, b⁻¹)` has determinant one, so it lies in `SU(2)`. -/
theorem det_unitaryTorusHom_inv (b : Circle) :
    (unitaryTorusHom (Fin 2) ![b, b⁻¹] : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := by
  rw [coe_unitaryTorusHom, Matrix.det_diagonal, Fin.prod_univ_two]
  simp

/-- The kernel of the central isogeny of the torus of `U(2)` is `{(1, 1), (-1, -1)}`. -/
theorem mem_ker_unitaryTorusCentralIsogeny_iff {p : Circle × Circle} :
    p ∈ unitaryTorusCentralIsogeny.ker ↔ p = 1 ∨ p = (-1, -1) := by
  obtain ⟨a, b⟩ := p
  rw [MonoidHom.mem_ker, ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_ofClass,
    unitaryTorusCentralIsogeny_apply]
  constructor
  · intro h
    simp only [Prod.mk_eq_one] at h
    -- `a b = 1` and `a b⁻¹ = 1` force `b = a` and `a² = 1`.
    have hb : b = a := by
      have := h.2
      rw [mul_inv_eq_one] at this
      exact this.symm
    subst hb
    have ha : ((b : ℂ)) * b = 1 := by rw [← Circle.coe_mul, h.1, Circle.coe_one]
    rcases mul_self_eq_one_iff.1 ha with ha | ha
    · exact Or.inl (by ext <;> simp [ha])
    · exact Or.inr (by ext <;> simp [ha])
  · rintro (h | h) <;> simp only [Prod.mk_eq_one, Prod.mk.injEq] at h ⊢
    · simp [h.1, h.2]
    · obtain ⟨rfl, rfl⟩ := h
      simp

/-- The kernel of the central isogeny of the torus of `U(2)` has two elements. -/
theorem card_ker_unitaryTorusCentralIsogeny : Nat.card unitaryTorusCentralIsogeny.ker = 2 := by
  have h : (unitaryTorusCentralIsogeny.ker : Set (Circle × Circle)) = {1, (-1, -1)} := by
    ext p
    rw [SetLike.mem_coe, mem_ker_unitaryTorusCentralIsogeny_iff]
    simp
  have hne : (1 : Circle × Circle) ≠ (-1, -1) := by
    simp [Prod.ext_iff, Circle.ext_iff, eq_comm, CharZero.eq_neg_self_iff]
  rw [← SetLike.coe_sort_coe, h, Nat.card_coe_set_eq, Set.ncard_pair hne]

/-- **The period lattices of the central isogeny of the torus of `U(2)`.** The period lattice
`Λ_ℤ(Z) ⊕ Λ_ℤ(T_ss)` of `Z × T_ss` has index two in the period lattice of the diagonal torus `T`
of `U(2)`: the splitting of the Lie algebra into its central and semisimple parts does not split
the period lattice integrally. -/
theorem relIndex_map_lieMap_unitaryTorusCentralIsogeny_periodLattice :
    ((periodLattice ((𝓡 1).prod (𝓡 1)) (Circle × Circle)).map
        (unitaryTorusCentralIsogeny.lieMap (I := (𝓡 1).prod (𝓡 1))
          (I' := (𝓡 1).prod (𝓡 1))).toLinearMap.toAddMonoidHom).relIndex
      (periodLattice ((𝓡 1).prod (𝓡 1)) (Circle × Circle)) = 2 := by
  have : Finite unitaryTorusCentralIsogeny.ker := Nat.finite_of_card_ne_zero (by
    rw [card_ker_unitaryTorusCentralIsogeny]; exact two_ne_zero)
  have : FiniteDimensional ℝ (LeftInvariantDerivation ((𝓡 1).prod (𝓡 1)) (Circle × Circle)) :=
    finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint
  -- The Lie map is injective because the kernel is finite, hence bijective in finite dimension.
  let L := (unitaryTorusCentralIsogeny.lieMap (I := (𝓡 1).prod (𝓡 1))
    (I' := (𝓡 1).prod (𝓡 1))).toLinearMap
  have hinj : Function.Injective L :=
    unitaryTorusCentralIsogeny.lieMap_injective_of_discreteTopology_ker
  rw [unitaryTorusCentralIsogeny.relIndex_map_lieMap_periodLattice
    ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩, card_ker_unitaryTorusCentralIsogeny]

end TauCeti
