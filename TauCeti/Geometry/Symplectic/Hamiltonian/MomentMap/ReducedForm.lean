/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.EquivariantMomentMap.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Level
public import TauCeti.Geometry.Symplectic.Manifold.Descent

/-!
# The reduced symplectic form on a quotient of a level of a moment map

Let `μ : M → 𝔤*` be a moment map of an infinitesimal action `Z ↦ Z_M` of a Lie algebra `𝔤` on a
manifold `M` with a closed two-form `σ`. Marsden–Weinstein–Meyer reduction at a value `c` takes
the level `μ⁻¹(c)`, divides it by the coadjoint stabilizer `G_c`, and puts on the quotient the
unique form whose pullback to the level is the restriction of `σ`. This file proves the last step
for a level and a quotient that are supplied as data, so that it applies to every construction of
the quotient (the free and proper quotient by `G_c`, or a principal bundle presented otherwise):

* the level is a manifold `Z` with a smooth map `i : Z → M` into `μ⁻¹(c)` whose tangent images are
  the kernels `ker dμ` (for a regular value this is the inclusion of the level);
* the quotient is a surjective smooth submersion `p : Z → Q` out of a boundaryless manifold, whose
  vertical directions `ker dp_z` are the tangent vectors that `di_z` sends into the stabilizer
  directions `𝔤_c · i z` (`TauCeti.lieAnnihilator`);
* a family `ψ` of smooth self-maps of `Z` over `p`, transitive on the fibres of `p` and preserving
  `i^* σ`, plays the role of the action of `G_c` on the level.

Where `σ` is nondegenerate and the cocycle of `μ` vanishes along the level, the kernel of `i^* σ` at
`z` is the preimage under `di_z` of `𝔤_c · i z`
(`TauCeti.SmoothTwoForm.IsMomentMap.ker_bilinFormAt_mpullback`), so it is exactly `ker dp_z`. In
particular `i^* σ` vanishes on vertical vectors. Being also invariant under `ψ`, it is basic for
`p` (`TauCeti.RoughForm.isBasic_of_mpullback_eq`), and since it is closed it descends to a unique
symplectic form on `Q` (`TauCeti.SmoothTwoForm.existsUnique_isSymplectic_mpullback_eq`):

`∃! ω_red, ω_red symplectic and p^* ω_red = i^* σ`

(`TauCeti.SmoothTwoForm.IsMomentMap.existsUnique_isSymplectic_mpullback_eq`). For a group-level
moment map of an action preserving `σ`, the cocycle vanishes everywhere, and the invariance of
`i^* σ` follows from `i (ψ_j z) = g_j • i z` for elements `g_j` of the group
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.existsUnique_isSymplectic_mpullback_eq`).

At a point where the action is moreover locally free, the reduced space has the expected dimension
`dim Q = dim M - dim 𝔤 - dim 𝔤_c`
(`TauCeti.SmoothTwoForm.IsMomentMap.finrank_eq_finrank_sub_finrank_sub_finrank_lieAnnihilator`);
for a coadjoint-fixed value, where `𝔤_c = 𝔤` (such as every value of a torus moment map), this is
`dim M - 2 dim 𝔤`.

## Main results

* `TauCeti.SmoothTwoForm.IsMomentMap.ker_bilinFormAt_mpullback_eq_ker_mfderiv`: the null
  directions of `i^* σ` are the vertical directions of `p`.
* `TauCeti.SmoothTwoForm.IsMomentMap.isBasic_mpullback`: `i^* σ` is basic for `p`.
* `TauCeti.SmoothTwoForm.IsMomentMap.existsUnique_isSymplectic_mpullback_eq`: the reduced
  symplectic form exists and is unique.
* `TauCeti.SmoothTwoForm.IsEquivariantMomentMap.existsUnique_isSymplectic_mpullback_eq`: the same
  for a group-level moment map, with the symmetries of the level covering group elements.
* `TauCeti.SmoothTwoForm.IsMomentMap.finrank_eq_finrank_sub_finrank_sub_finrank_lieAnnihilator`:
  the dimension of the reduced space.

## References

* J. Marsden, A. Weinstein, *Reduction of symplectic manifolds with symmetry*, Reports on
  Mathematical Physics 5 (1974), 121–130.
* K. Meyer, *Symmetries and integrals in mechanics*, in *Dynamical Systems* (M. Peixoto, ed.),
  Academic Press, 1973, 259–273.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lecture 23 (the proof of the Marsden–Weinstein–Meyer theorem).
-/

public section

noncomputable section

open Function Manifold Module
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

namespace IsMomentMap

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {σ : SmoothTwoForm I M} {a : InfinitesimalAction 𝔤 I M} {μ : M → Module.Dual ℝ 𝔤}
  {EZ HZ Z : Type*} [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [TopologicalSpace HZ]
  {J : ModelWithCorners ℝ EZ HZ} [TopologicalSpace Z] [ChartedSpace HZ Z] [IsManifold J ∞ Z]
  {EQ HQ Q : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
  {K : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q] [IsManifold K ∞ Q]
  {i : Z → M} {p : Z → Q} {c : Module.Dual ℝ 𝔤}

omit [IsManifold K ∞ Q] in
/-- **The null directions of the form on a level are the vertical directions of its quotient.**
Let `i : Z → M` parametrize the level `μ⁻¹(c)`, with tangent image `ker dμ` at `z`, and let the
vertical directions of `p : Z → Q` at `z` be the vectors that `di_z` sends into the stabilizer
directions `𝔤_c · i z`. Where `σ` is nondegenerate and the cocycle of `μ` vanishes, the kernel of
`i^* σ` at `z` is the kernel of `dp_z`. -/
theorem ker_bilinFormAt_mpullback_eq_ker_mfderiv [FiniteDimensional ℝ E] (h : σ.IsMomentMap a μ)
    (hi : ContMDiff J I ∞ i) {z : Z} (hσ : (σ.bilinFormAt (i z)).Nondegenerate)
    (hc : σ.momentCocycle a μ (i z) = 0) (hμ : μ (i z) = c)
    (hrange : LinearMap.range (mfderiv J I i z).toLinearMap =
      LinearMap.ker (h.differential (i z)))
    (hker : (mfderiv J K p z).ker =
      ((lieAnnihilator ℝ 𝔤 c).toSubmodule.map (a.eval (i z))).comap
        (mfderiv J I i z).toLinearMap) :
    LinearMap.ker ((SmoothForm.mpullback i hi σ).bilinFormAt z) = (mfderiv J K p z).ker := by
  rw [h.ker_bilinFormAt_mpullback hi hσ hc hrange, hμ, hker]

omit [IsManifold K ∞ Q] in
/-- **The form restricted to a level is basic for its quotient.** Under the hypotheses of
`TauCeti.SmoothTwoForm.IsMomentMap.ker_bilinFormAt_mpullback_eq_ker_mfderiv` at every point, let
`ψ` be a family of smooth self-maps of `Z` over `p`, transitive on the fibres of `p`, that
preserve `i^* σ`. Then `i^* σ` is basic for `p`. -/
theorem isBasic_mpullback [FiniteDimensional ℝ E] (h : σ.IsMomentMap a μ)
    (hi : ContMDiff J I ∞ i) (hσ : ∀ z, (σ.bilinFormAt (i z)).Nondegenerate)
    (hc : ∀ z, σ.momentCocycle a μ (i z) = 0) (hμ : ∀ z, μ (i z) = c)
    (hrange : ∀ z, LinearMap.range (mfderiv J I i z).toLinearMap =
      LinearMap.ker (h.differential (i z)))
    (hp : ContMDiff J K ∞ p)
    (hker : ∀ z, (mfderiv J K p z).ker =
      ((lieAnnihilator ℝ 𝔤 c).toSubmodule.map (a.eval (i z))).comap
        (mfderiv J I i z).toLinearMap)
    {ι : Type*} {ψ : ι → Z → Z} (hψ : ∀ j, ContMDiff J J ∞ (ψ j)) (hpψ : ∀ j, p ∘ ψ j = p)
    (hψp : ∀ z z', p z = p z' → z = z' ∨ ∃ j, ψ j z = z')
    (hinv : ∀ j, SmoothForm.mpullback (ψ j) (hψ j) (SmoothForm.mpullback i hi σ) =
      SmoothForm.mpullback i hi σ) :
    RoughForm.IsBasic (V := ℝ) (k := 2) K p (SmoothForm.mpullback i hi σ).1 := by
  refine RoughForm.isBasic_of_mpullback_eq (hp.mdifferentiable (by simp))
    (fun j ↦ (hψ j).mdifferentiable (by simp)) hpψ hψp
    (fun j ↦ by simpa only [SmoothForm.coe_mpullback] using congrArg Subtype.val (hinv j))
    fun z v j hj ↦ ?_
  -- A vertical vector lies in the kernel of `i^* σ`, and a two-form vanishes on such a pair.
  have hmem : v j ∈ LinearMap.ker ((SmoothForm.mpullback i hi σ).bilinFormAt z) := by
    rw [h.ker_bilinFormAt_mpullback_eq_ker_mfderiv hi (hσ z) (hc z) (hμ z) (hrange z) (hker z)]
    exact hj
  have hv : v = ![v 0, v 1] := by
    ext k
    fin_cases k <;> rfl
  rw [LinearMap.mem_ker] at hmem
  rw [hv, ← SmoothBundleForm.eval₂_apply, ← SmoothForm.bilinFormAt_apply]
  fin_cases j
  · exact LinearMap.congr_fun hmem _
  · exact (SmoothForm.isAlt_bilinFormAt _ z).eq_iff.2 (LinearMap.congr_fun hmem _)

/-- **Marsden–Weinstein–Meyer reduction on a quotient of a level.** Let `σ` be closed, let
`i : Z → M` parametrize the level `μ⁻¹(c)` of a moment map with tangent images `ker dμ`, along
which `σ` is nondegenerate and the cocycle of `μ` vanishes, and let `p : Z → Q` be a surjective
smooth submersion out of a boundaryless manifold whose vertical directions at `z` are the vectors
that `di_z` sends into the stabilizer directions `𝔤_c · i z`. If a family `ψ` of smooth self-maps
of `Z` over `p`, transitive on the fibres of `p`, preserves `i^* σ`, then there is exactly one
symplectic form `ω_red` on `Q` with `p^* ω_red = i^* σ`. -/
theorem existsUnique_isSymplectic_mpullback_eq [FiniteDimensional ℝ E] [J.Boundaryless]
    (h : σ.IsMomentMap a μ) (hσc : σ.IsClosed) (hi : ContMDiff J I ∞ i)
    (hσ : ∀ z, (σ.bilinFormAt (i z)).Nondegenerate) (hc : ∀ z, σ.momentCocycle a μ (i z) = 0)
    (hμ : ∀ z, μ (i z) = c)
    (hrange : ∀ z, LinearMap.range (mfderiv J I i z).toLinearMap =
      LinearMap.ker (h.differential (i z)))
    (hp : IsSubmersion J K ∞ p) (hsurj : Surjective p)
    (hker : ∀ z, (mfderiv J K p z).ker =
      ((lieAnnihilator ℝ 𝔤 c).toSubmodule.map (a.eval (i z))).comap
        (mfderiv J I i z).toLinearMap)
    {ι : Type*} {ψ : ι → Z → Z} (hψ : ∀ j, ContMDiff J J ∞ (ψ j)) (hpψ : ∀ j, p ∘ ψ j = p)
    (hψp : ∀ z z', p z = p z' → z = z' ∨ ∃ j, ψ j z = z')
    (hinv : ∀ j, SmoothForm.mpullback (ψ j) (hψ j) (SmoothForm.mpullback i hi σ) =
      SmoothForm.mpullback i hi σ) :
    ∃! η : SmoothTwoForm K Q,
      η.IsSymplectic ∧ SmoothForm.mpullback p hp.contMDiff η = SmoothForm.mpullback i hi σ :=
  SmoothTwoForm.existsUnique_isSymplectic_mpullback_eq hp hsurj (hσc.mpullback i hi)
    (h.isBasic_mpullback hi hσ hc hμ hrange hp.contMDiff hker hψ hpψ hψp hinv)
    fun z ↦ h.ker_bilinFormAt_mpullback_eq_ker_mfderiv hi (hσ z) (hc z) (hμ z) (hrange z) (hker z)

omit [IsManifold J ∞ Z] [IsManifold K ∞ Q] in
/-- **The dimension of the reduced space.** Under the hypotheses of
`TauCeti.SmoothTwoForm.IsMomentMap.ker_bilinFormAt_mpullback_eq_ker_mfderiv` at a point `z` where
`dp_z` is surjective and the action is locally free, the quotient has dimension
`dim M - dim 𝔤 - dim 𝔤_c`. -/
theorem finrank_eq_finrank_sub_finrank_sub_finrank_lieAnnihilator [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ EZ] (h : σ.IsMomentMap a μ) {z : Z}
    (hσ : (σ.bilinFormAt (i z)).Nondegenerate) (hc : σ.momentCocycle a μ (i z) = 0)
    (hμ : μ (i z) = c)
    (hrange : LinearMap.range (mfderiv J I i z).toLinearMap =
      LinearMap.ker (h.differential (i z)))
    (hp : Surjective (mfderiv J K p z))
    (hker : (mfderiv J K p z).ker =
      ((lieAnnihilator ℝ 𝔤 c).toSubmodule.map (a.eval (i z))).comap
        (mfderiv J I i z).toLinearMap)
    (hfree : a.isotropy (i z) = ⊥) :
    finrank ℝ EQ = finrank ℝ E - finrank ℝ 𝔤 - finrank ℝ (lieAnnihilator ℝ 𝔤 c) := by
  set T := LinearMap.ker (h.differential (i z))
  set S := (lieAnnihilator ℝ 𝔤 c).toSubmodule.map (a.eval (i z))
  have hST : S ≤ T := by
    have hnull := h.ker_differential_inf_orthogonal hσ hc
    rw [hμ] at hnull
    exact hnull.ge.trans inf_le_left
  -- `di_z`, as a map onto the level tangent space `T`, followed by the quotient by `S`.
  let d : TangentSpace J z →ₗ[ℝ] T :=
    (mfderiv J I i z).toLinearMap.codRestrict T fun v ↦ hrange ▸ LinearMap.mem_range_self _ v
  let S' : Submodule ℝ T := S.comap T.subtype
  let g := S'.mkQ ∘ₗ d
  have hd : Surjective d := fun ⟨w, hw⟩ ↦ by
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.1 (hrange ▸ hw : w ∈ LinearMap.range _)
    exact ⟨v, rfl⟩
  have hg : LinearMap.range g = ⊤ :=
    LinearMap.range_eq_top.2 ((Submodule.mkQ_surjective S').comp hd)
  have hkerg : LinearMap.ker g = LinearMap.ker (mfderiv J K p z).toLinearMap := by
    ext v
    simp only [g, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, S', Submodule.mem_comap, Submodule.subtype_apply, d,
      LinearMap.codRestrict_apply]
    rw [← LinearMap.mem_ker, hker, Submodule.mem_comap]
  have h₁ := g.finrank_range_add_finrank_ker
  have h₂ := (mfderiv J K p z).toLinearMap.finrank_range_add_finrank_ker
  rw [hg, finrank_top, hkerg] at h₁
  rw [LinearMap.range_eq_top.2 hp, finrank_top] at h₂
  have h₃ := Submodule.finrank_quotient_add_finrank S'
  have h₄ : finrank ℝ S' = finrank ℝ S :=
    (Submodule.comapSubtypeEquivOfLe hST).finrank_eq
  have h₅ : finrank ℝ T - finrank ℝ S =
      finrank ℝ E - finrank ℝ 𝔤 - finrank ℝ (lieAnnihilator ℝ 𝔤 c) := by
    have h' := h.finrank_ker_differential_sub_finrank_inf_orthogonal hσ hc hfree
    rwa [h.ker_differential_inf_orthogonal hσ hc, hμ] at h'
  -- `h₂` counts dimensions in the tangent space of `Q` at `p z`, which is its model space `EQ`.
  change finrank ℝ (TangentSpace K (p z)) = _
  omega

end IsMomentMap

namespace IsEquivariantMomentMap

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I (minSmoothness ℝ 3) G]
  [LieGroup I ∞ G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [MulAction G M]
  [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}
  {EZ HZ Z : Type*} [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [TopologicalSpace HZ]
  {J : ModelWithCorners ℝ EZ HZ} [TopologicalSpace Z] [ChartedSpace HZ Z] [IsManifold J ∞ Z]
  {EQ HQ Q : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
  {K : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q] [IsManifold K ∞ Q]
  {i : Z → M} {p : Z → Q} {c : Module.Dual ℝ (GroupLieAlgebra I G)}

/-- **Marsden–Weinstein–Meyer reduction for a group-level moment map.** Let a Lie group `G` act
smoothly on `M`, preserving a closed two-form `σ`, with a coadjoint-equivariant moment map `μ`.
Let `i : Z → M` parametrize the level `μ⁻¹(c)` with tangent images `ker dμ`, along which `σ` is
nondegenerate, and let `p : Z → Q` be a surjective smooth submersion out of a boundaryless manifold
whose vertical directions at `z` are the vectors that `di_z` sends into the stabilizer directions
`𝔤_c · i z`. If a family `ψ` of smooth self-maps of `Z` over `p`, transitive on the fibres of `p`,
covers group elements, `i (ψ_j z) = g_j • i z`, then there is exactly one symplectic form `ω_red`
on `Q` with `p^* ω_red = i^* σ`. -/
theorem existsUnique_isSymplectic_mpullback_eq [J.Boundaryless] (h : σ.IsEquivariantMomentMap μ)
    (hσG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (hσc : σ.IsClosed) (hi : ContMDiff J I' ∞ i)
    (hσ : ∀ z, (σ.bilinFormAt (i z)).Nondegenerate) (hμ : ∀ z, μ (i z) = c)
    (hrange : ∀ z, LinearMap.range (mfderiv J I' i z).toLinearMap =
      LinearMap.ker (h.differential (i z)))
    (hp : IsSubmersion J K ∞ p) (hsurj : Surjective p)
    (hker : ∀ z, (mfderiv J K p z).ker =
      ((lieAnnihilator ℝ (GroupLieAlgebra I G) c).toSubmodule.map
        ((InfinitesimalAction.fundamental I G I' M).eval (i z))).comap
        (mfderiv J I' i z).toLinearMap)
    {ι : Type*} {ψ : ι → Z → Z} (hψ : ∀ j, ContMDiff J J ∞ (ψ j)) (hpψ : ∀ j, p ∘ ψ j = p)
    (hψp : ∀ z z', p z = p z' → z = z' ∨ ∃ j, ψ j z = z') {g : ι → G}
    (hiψ : ∀ j z, i (ψ j z) = g j • i z) :
    ∃! η : SmoothTwoForm K Q,
      η.IsSymplectic ∧ SmoothForm.mpullback p hp.contMDiff η = SmoothForm.mpullback i hi σ := by
  refine h.toIsMomentMap.existsUnique_isSymplectic_mpullback_eq hσc hi hσ
    (fun z ↦ h.momentCocycle_eq_zero (i z)) hμ hrange hp hsurj hker hψ hpψ hψp fun j ↦ ?_
  -- `i ∘ ψ_j` is `i` followed by the action of `g_j`, which preserves `σ`.
  have hcomp : i ∘ ψ j = (fun x : M ↦ g j • x) ∘ i := funext (hiψ j)
  nth_rewrite 2 [← hσG (g j)]
  rw [SmoothForm.mpullback_mpullback, SmoothForm.mpullback_mpullback]
  simp only [hcomp]

end IsEquivariantMomentMap

end SmoothTwoForm

end TauCeti
