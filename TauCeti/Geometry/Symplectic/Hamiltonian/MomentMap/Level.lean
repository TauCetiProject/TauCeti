/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap
public import TauCeti.Geometry.Symplectic.Lagrangian.Basic
import TauCeti.Geometry.Manifold.IsManifold.Basic

/-!
# The symplectic form on the levels of a moment map

Let `μ : M → 𝔤*` be a moment map of an infinitesimal action `Z ↦ Z_M` of a Lie algebra `𝔤` on a
manifold `M` with a two-form `σ`, in the convention `ι_{Z_M} σ = d⟨μ, Z⟩`
(`TauCeti.SmoothTwoForm.IsMomentMap`). Let `x ∈ M` be a point at which `μ` is infinitesimally
equivariant, that is, its cocycle `σ(Z_M, Z'_M) - μ_{⁅Z, Z'⁆}` vanishes at `x`; this holds at every
point for a coadjoint-equivariant moment map of a Lie group action
(`TauCeti.SmoothTwoForm.IsEquivariantMomentMap.momentCocycle_eq_zero`). Write `c = μ(x)` and
`𝔤_c = {Z | ⁅Z, c⁆ = 0}` for its coadjoint stabilizer (`TauCeti.lieAnnihilator ℝ 𝔤 c`).

The kernel `ker dμ_x` is the tangent space at `x` of the level `μ⁻¹(c)` when `c` is a regular
value. This file describes the restriction of `σ_x` to it. These are pointwise linear-algebra
ingredients of Marsden–Weinstein–Meyer reduction, where the null directions of `σ` on the level are
exactly the directions of the orbits of the stabilizer. No quotient is constructed here: that the
reduced space `μ⁻¹(c) / G_c` is a symplectic manifold additionally needs `σ` closed, `c` a regular
value, and the stabilizer `G_c` acting freely and properly on the level.

* Since `dμ_x(Z_M x) = ⁅Z, c⁆`, the orbit directions tangent to the level are those of the
  stabilizer: `𝔤 · x ∩ ker dμ_x = 𝔤_c · x`
  (`TauCeti.SmoothTwoForm.IsMomentMap.orbitTangent_inf_ker_differential`).
* Where `σ_x` is nondegenerate, `ker dμ_x = (𝔤 · x)^σ`, so the symplectic complement of the level
  tangent space is the orbit tangent space
  (`TauCeti.SmoothTwoForm.IsMomentMap.orthogonal_ker_differential`), and the **null directions**
  `ker dμ_x ∩ (ker dμ_x)^σ` of `σ` on the level are `𝔤_c · x`
  (`TauCeti.SmoothTwoForm.IsMomentMap.ker_differential_inf_orthogonal`).
* The level is coisotropic at `x`, equivalently the orbit tangent space is isotropic, exactly when
  `c` is fixed by the coadjoint action, `𝔤_c = 𝔤`
  (`TauCeti.SmoothTwoForm.IsMomentMap.isCoisotropic_ker_differential_iff` and
  `TauCeti.SmoothTwoForm.IsMomentMap.isIsotropic_orbitTangent_iff`). A level over a value that
  is not coadjoint-fixed is not coisotropic. For an abelian Lie algebra every value is fixed, so
  the orbits are isotropic, and a locally free action of an abelian `𝔤` has
  `2 dim 𝔤 ≤ dim M` (`TauCeti.SmoothTwoForm.IsMomentMap.two_mul_finrank_le`).
* At a point where the action is locally free, `dim ker dμ_x = dim M - dim 𝔤` and the null
  directions have dimension `dim 𝔤_c`, so the linear quotient of the level tangent space by them
  has dimension `dim M - dim 𝔤 - dim 𝔤_c`; under the hypotheses of the reduction theorem this
  is the dimension of the reduced space
  (`TauCeti.SmoothTwoForm.IsMomentMap.finrank_ker_differential_sub_finrank_inf_orthogonal`).
* For a smooth map `g : N → M` whose tangent images are the kernels of `dμ`, such as the inclusion
  of a regular level, the kernel of the pulled-back form `g^* σ` at `p` is the preimage under
  `dg_p` of `𝔤_c · g(p)` (`TauCeti.SmoothTwoForm.IsMomentMap.ker_bilinFormAt_mpullback`). This is
  the kernel condition for `g^* σ` to descend along the quotient by the stabilizer.

## References

* J. Marsden, A. Weinstein, *Reduction of symplectic manifolds with symmetry*, Reports on
  Mathematical Physics 5 (1974), 121–130.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lecture 23 (the proof of the Marsden–Weinstein–Meyer theorem).
* V. Guillemin, S. Sternberg, *Symplectic Techniques in Physics*, Cambridge University Press,
  1984, Section 26.
-/

public section

noncomputable section

open Module
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

namespace IsMomentMap

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {σ : SmoothTwoForm I M} {a : InfinitesimalAction 𝔤 I M} {μ : M → Module.Dual ℝ 𝔤}
  (h : σ.IsMomentMap a μ) {x : M}

include h

/-! ### Orbit directions tangent to a level -/

/-- **The orbit directions tangent to a level are those of the stabilizer.** Where the cocycle of
a moment map vanishes, `𝔤 · x ∩ ker dμ_x = 𝔤_{μ(x)} · x`. -/
theorem orbitTangent_inf_ker_differential (hc : σ.momentCocycle a μ x = 0) :
    a.orbitTangent x ⊓ LinearMap.ker (h.differential x) =
      (lieAnnihilator ℝ 𝔤 (μ x)).toSubmodule.map (a.eval x) := by
  ext v
  simp only [Submodule.mem_inf, InfinitesimalAction.mem_orbitTangent_iff, LinearMap.mem_ker,
    Submodule.mem_map, LieSubalgebra.mem_toSubmodule, mem_lieAnnihilator,
    InfinitesimalAction.eval_apply]
  constructor
  · rintro ⟨⟨Z, rfl⟩, hZ⟩
    exact ⟨Z, by rwa [← h.differential_apply_of_momentCocycle_eq_zero hc], rfl⟩
  · rintro ⟨Z, hZ, rfl⟩
    exact ⟨⟨Z, rfl⟩, by rwa [h.differential_apply_of_momentCocycle_eq_zero hc]⟩

/-- Where the cocycle of a moment map vanishes, the orbit tangent space lies in `ker dμ_x` exactly
when `μ(x)` is fixed by the coadjoint action of `𝔤`. -/
theorem orbitTangent_le_ker_differential_iff (hc : σ.momentCocycle a μ x = 0) :
    a.orbitTangent x ≤ LinearMap.ker (h.differential x) ↔ lieAnnihilator ℝ 𝔤 (μ x) = ⊤ := by
  constructor
  · intro hle
    refine eq_top_iff.2 fun Z _ ↦ (mem_lieAnnihilator ℝ 𝔤).2 ?_
    rw [← h.differential_apply_of_momentCocycle_eq_zero hc]
    exact hle (a.mem_orbitTangent x Z)
  · intro htop v hv
    obtain ⟨Z, rfl⟩ := (a.mem_orbitTangent_iff x).1 hv
    rw [LinearMap.mem_ker, h.differential_apply_of_momentCocycle_eq_zero hc]
    exact (mem_lieAnnihilator ℝ 𝔤).1 (htop ▸ LieSubalgebra.mem_top Z)

/-! ### Null directions of the form on a level -/

/-- **The symplectic complement of a level is the orbit.** Where the form is nondegenerate, the
`σ_x`-orthogonal of `ker dμ_x` is the orbit tangent space `𝔤 · x`. -/
theorem orthogonal_ker_differential [FiniteDimensional ℝ E]
    (hσx : (σ.bilinFormAt x).Nondegenerate) :
    (σ.bilinFormAt x).orthogonal (LinearMap.ker (h.differential x)) = a.orbitTangent x := by
  rw [h.ker_differential, LinearMap.BilinForm.orthogonal_orthogonal hσx
    (SmoothForm.isAlt_bilinFormAt σ x).isRefl]

/-- **The null directions of the form on a level are the stabilizer directions.** Where the form
is nondegenerate and the cocycle of a moment map vanishes, the kernel of `σ_x` restricted to
`ker dμ_x` is `𝔤_{μ(x)} · x`. -/
theorem ker_differential_inf_orthogonal [FiniteDimensional ℝ E]
    (hσx : (σ.bilinFormAt x).Nondegenerate) (hc : σ.momentCocycle a μ x = 0) :
    LinearMap.ker (h.differential x) ⊓
        (σ.bilinFormAt x).orthogonal (LinearMap.ker (h.differential x)) =
      (lieAnnihilator ℝ 𝔤 (μ x)).toSubmodule.map (a.eval x) := by
  rw [h.orthogonal_ker_differential hσx, inf_comm, h.orbitTangent_inf_ker_differential hc]

variable (hσ : σ.IsNondegenerate)

/-- **Levels over coadjoint-fixed values are coisotropic, and only those.** For a nondegenerate
form, where the cocycle of a moment map vanishes, `ker dμ_x` is coisotropic exactly when `μ(x)` is
fixed by the coadjoint action of `𝔤`. -/
theorem isCoisotropic_ker_differential_iff [FiniteDimensional ℝ E]
    (hc : σ.momentCocycle a μ x = 0) :
    (hσ.symplecticFormAt x).IsCoisotropic (LinearMap.ker (h.differential x)) ↔
      lieAnnihilator ℝ 𝔤 (μ x) = ⊤ := by
  rw [SymplecticForm.isCoisotropic_iff_le, SymplecticForm.orthogonal_def,
    hσ.toBilinForm_symplecticFormAt, h.orthogonal_ker_differential (hσ.nondegenerate_bilinFormAt x),
    h.orbitTangent_le_ker_differential_iff hc]

/-- **Orbits in levels over coadjoint-fixed values are isotropic, and only those.** For a
nondegenerate form, where the cocycle of a moment map vanishes, the orbit tangent space `𝔤 · x` is
isotropic exactly when `μ(x)` is fixed by the coadjoint action of `𝔤`. -/
theorem isIsotropic_orbitTangent_iff (hc : σ.momentCocycle a μ x = 0) :
    (hσ.symplecticFormAt x).IsIsotropic (a.orbitTangent x) ↔ lieAnnihilator ℝ 𝔤 (μ x) = ⊤ := by
  rw [SymplecticForm.isIsotropic_iff_le, SymplecticForm.orthogonal_def,
    hσ.toBilinForm_symplecticFormAt, ← h.ker_differential,
    h.orbitTangent_le_ker_differential_iff hc]

/-- **The orbits of an abelian Lie algebra are isotropic.** For a nondegenerate form, where the
cocycle of a moment map of an action of an abelian Lie algebra vanishes, the orbit tangent space
is isotropic. -/
theorem isIsotropic_orbitTangent [IsLieAbelian 𝔤] (hc : σ.momentCocycle a μ x = 0) :
    (hσ.symplecticFormAt x).IsIsotropic (a.orbitTangent x) :=
  (h.isIsotropic_orbitTangent_iff hσ hc).2 (lieAnnihilator_eq_top ℝ 𝔤 _)

/-- **The dimension bound for abelian actions.** If an abelian Lie algebra acts locally freely at
`x` with a moment map whose cocycle vanishes there, and the form is nondegenerate at `x`, then
`2 dim 𝔤 ≤ dim M`. -/
theorem two_mul_finrank_le [FiniteDimensional ℝ E] [IsLieAbelian 𝔤]
    (hσx : (σ.bilinFormAt x).Nondegenerate) (hc : σ.momentCocycle a μ x = 0)
    (hfree : a.isotropy x = ⊥) :
    2 * finrank ℝ 𝔤 ≤ finrank ℝ E := by
  have hle := Submodule.finrank_mono
    ((h.orbitTangent_le_ker_differential_iff hc).2 (lieAnnihilator_eq_top ℝ 𝔤 _))
  have hsum := h.finrank_ker_differential_add_finrank_orbitTangent hσx
  rw [a.finrank_orbitTangent_of_isotropy_eq_bot x hfree] at hle
  rw [a.finrank_orbitTangent_of_isotropy_eq_bot x hfree, finrank_tangentSpace] at hsum
  omega

/-! ### Dimensions at a locally free point -/

/-- Where the form is nondegenerate and the action is locally free, the level tangent space
`ker dμ_x` has codimension `dim 𝔤`. -/
theorem finrank_ker_differential_add_finrank [FiniteDimensional ℝ E]
    (hσx : (σ.bilinFormAt x).Nondegenerate) (hfree : a.isotropy x = ⊥) :
    finrank ℝ (LinearMap.ker (h.differential x)) + finrank ℝ 𝔤 = finrank ℝ E := by
  have := h.finrank_ker_differential_add_finrank_orbitTangent hσx
  rwa [a.finrank_orbitTangent_of_isotropy_eq_bot x hfree, finrank_tangentSpace] at this

/-- Where the form is nondegenerate, the cocycle of a moment map vanishes and the action is
locally free, the null directions of the form on a level have the dimension of the stabilizer
`𝔤_{μ(x)}`. -/
theorem finrank_ker_differential_inf_orthogonal [FiniteDimensional ℝ E]
    (hσx : (σ.bilinFormAt x).Nondegenerate) (hc : σ.momentCocycle a μ x = 0)
    (hfree : a.isotropy x = ⊥) :
    finrank ℝ ↥(LinearMap.ker (h.differential x) ⊓
        (σ.bilinFormAt x).orthogonal (LinearMap.ker (h.differential x))) =
      finrank ℝ (lieAnnihilator ℝ 𝔤 (μ x)) := by
  rw [h.ker_differential_inf_orthogonal hσx hc]
  exact (Submodule.equivMapOfInjective _ ((a.isotropy_eq_bot_iff x).1 hfree) _).finrank_eq.symm

/-- **The dimension of the linear quotient by the null directions.** Where the form is
nondegenerate, the cocycle of a
moment map vanishes and the action is locally free, the quotient of the level tangent space
`ker dμ_x` by the null directions of the form has dimension `dim M - dim 𝔤 - dim 𝔤_{μ(x)}`. -/
theorem finrank_ker_differential_sub_finrank_inf_orthogonal [FiniteDimensional ℝ E]
    (hσx : (σ.bilinFormAt x).Nondegenerate) (hc : σ.momentCocycle a μ x = 0)
    (hfree : a.isotropy x = ⊥) :
    finrank ℝ (LinearMap.ker (h.differential x)) -
        finrank ℝ ↥(LinearMap.ker (h.differential x) ⊓
          (σ.bilinFormAt x).orthogonal (LinearMap.ker (h.differential x))) =
      finrank ℝ E - finrank ℝ 𝔤 - finrank ℝ (lieAnnihilator ℝ 𝔤 (μ x)) := by
  have h₁ := h.finrank_ker_differential_add_finrank hσx hfree
  rw [h.finrank_ker_differential_inf_orthogonal hσx hc hfree]
  omega

/-! ### The pulled-back form on a parametrized level -/

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

/-- **The kernel of the form pulled back to a level.** Let `g : N → M` be a smooth map whose
tangent image at `p` is the kernel of `dμ` at `g p`, such as the inclusion of a regular level of
`μ`. Where the form is nondegenerate at `g p` and the cocycle of the moment map vanishes there,
the kernel of `g^* σ` at `p` consists of the tangent vectors that `dg_p` sends into
`𝔤_{μ(g p)} · g p`. -/
theorem ker_bilinFormAt_mpullback [FiniteDimensional ℝ E] {g : N → M} (hg : ContMDiff J I ∞ g)
    {p : N} (hσx : (σ.bilinFormAt (g p)).Nondegenerate) (hc : σ.momentCocycle a μ (g p) = 0)
    (hrange : LinearMap.range (mfderiv J I g p).toLinearMap =
      LinearMap.ker (h.differential (g p))) :
    LinearMap.ker ((SmoothForm.mpullback g hg σ).bilinFormAt p) =
      ((lieAnnihilator ℝ 𝔤 (μ (g p))).toSubmodule.map (a.eval (g p))).comap
        (mfderiv J I g p).toLinearMap := by
  rw [← h.ker_differential_inf_orthogonal hσx hc, ← hrange]
  ext v
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.mem_inf, LinearMap.mem_range,
    exists_apply_eq_apply, true_and, LinearMap.BilinForm.mem_orthogonal_iff, forall_exists_index,
    forall_apply_eq_imp_iff, ContinuousLinearMap.coe_coe, LinearMap.ext_iff,
    SmoothForm.bilinFormAt_apply, SmoothForm.eval₂_mpullback, LinearMap.zero_apply]
  refine forall_congr' fun w ↦ ?_
  rw [← SmoothForm.bilinFormAt_apply, ← SmoothForm.bilinFormAt_apply,
    (SmoothForm.isAlt_bilinFormAt σ (g p)).eq_iff]

end IsMomentMap

end SmoothTwoForm

end TauCeti
