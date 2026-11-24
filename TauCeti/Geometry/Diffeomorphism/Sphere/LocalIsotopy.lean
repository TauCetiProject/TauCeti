/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Analysis.Normed.Module.Ball.Radial.Cone
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
public import TauCeti.Geometry.Diffeomorphism.Group
public import TauCeti.Geometry.Diffeomorphism.Topology
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.SinSqWeight
public import TauCeti.Geometry.Manifold.Diffeomorph.Perturbation
import TauCeti.Analysis.InnerProductSpace.Normalize
import TauCeti.Analysis.Normed.Module.Normalize
import TauCeti.Geometry.Diffeomorphism.Composition
import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Group
import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Path
import TauCeti.Geometry.Manifold.ContMDiffMap.WeakWhitney.Open
import TauCeti.Geometry.Manifold.Instances.Sphere

/-!
# Diffeomorphisms of a sphere near the identity are diffeotopic to it

Let `Sⁿ` be the unit sphere of a real inner product space `E` of dimension `n + 1`, and let `f` be
a `C^k` diffeomorphism of `Sⁿ`, `1 ≤ k`. Its displacement `x ↦ f x - x` extends to `E` as the cone
`u = TauCeti.sphereCone (fun x ↦ f x - x)`, positively homogeneous of degree one. When `u` is
`L`-Lipschitz with `L < 1`, every map `y ↦ y + c • u y`, `0 ≤ c ≤ 1`, is a homeomorphism of `E`
(`LipschitzWith.idAddSmulHomeomorph`) commuting with positive dilations, so

`x ↦ (x + c • (f x - x)) / ‖x + c • (f x - x)‖`

is a bijection of `Sⁿ`, with inverse the normalized inverse of `y ↦ y + c • u y`. Running `c` from
`0` to `1` along the analytic weight `TauCeti.sinSqWeight t = sin (π t / 2) ^ 2` gives a diffeotopy
from the identity to `f` (`TauCeti.sphereInterpolationDiffeotopy`): away from the origin, where `u`
is `C^k`, the inverses of `y ↦ y + c(t) • u y` depend smoothly on `(t, y)` by the parametric inverse
function theorem (`LipschitzWith.contDiffAt_idAddSmulHomeomorph_symm`).

The weak Whitney topology controls the first derivatives of `f` on the sphere, read in `E` through
the radial projection of the punctured space, so for `f` near the identity the displacement is
small and `1 / 4`-Lipschitz, and its cone is `5 / 8`-Lipschitz (`TauCeti.lipschitzWith_sphereCone`).
This is the **local isotopy lemma** for spheres: every diffeomorphism in a neighbourhood of the
identity of `Diff(Sⁿ)` is the final diffeomorphism of a diffeotopy
(`TauCeti.eventually_exists_diffeotopy_final_eq`). So the final diffeomorphisms of diffeotopies,
the range of the homomorphism `TauCeti.Diffeotopy.finalHom`, form a subgroup of `Diff(Sⁿ)`
which is a neighbourhood of the identity, hence open and closed: two diffeomorphisms of `Sⁿ` are
joined by a path in the weak Whitney topology exactly when they differ
by the final diffeomorphism of a diffeotopy (`TauCeti.joined_iff_exists_diffeotopy_mul_final_eq`).
So the path components of the group of `C^k` diffeomorphisms of `Sⁿ` are its `C^k` diffeotopy
classes.

## Main definitions

* `TauCeti.sphereInterpolationDiffeotopy`: the diffeotopy
  `(t, x) ↦ normalize (x + sin (π t / 2) ^ 2 • (f x - x))` from the identity to a diffeomorphism
  `f` of the sphere whose displacement has a cone of Lipschitz constant less than one.

## Main results

* `TauCeti.coe_sphereInterpolationDiffeotopy_apply`, `TauCeti.sphereInterpolationDiffeotopy_final`:
  the formula of the diffeotopy, and that it ends at `f`.
* `TauCeti.coe_sphereInterpolationDiffeotopy_symm_apply`: the formula of its inverse slices.
* `TauCeti.eventually_exists_diffeotopy_final_eq`: the local isotopy lemma.
* `TauCeti.joined_iff_exists_diffeotopy_mul_final_eq`: the path components of the group of `C^k`
  diffeomorphisms of `Sⁿ` are its `C^k` diffeotopy classes.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 2, §1, for the weak `C^k`
  topology, and Chapter 8, §8.1, for isotopies.
-/

public section

noncomputable section

open Metric Module Set Filter Topology TopologicalSpace NormedSpace
open scoped Manifold ContDiff NNReal unitInterval TauCeti.ManifoldWeakWhitney
  TauCeti.DiffeomorphWeakWhitney

namespace TauCeti

variable {k : ℕ∞ω}

/-! ### The interpolating homeomorphisms of a Banach space -/

section Interpolation

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] {u : V → V}
  {L : ℝ≥0}

/-- The homeomorphism `y ↦ y + sinSqWeight s • u y` of `V`. -/
private def slice (hu : LipschitzWith L u) (hL : L < 1) (s : ℝ) : V ≃ₜ V :=
  hu.idAddSmulHomeomorph hL (sinSqWeight s) (norm_sinSqWeight_le_one s)

private theorem slice_apply (hu : LipschitzWith L u) (hL : L < 1) (s : ℝ) (y : V) :
    slice hu hL s y = y + sinSqWeight s • u y := by
  simp only [slice, LipschitzWith.coe_idAddSmulHomeomorph]

/-- A slice fixes the origin when `u` does. -/
private theorem slice_ne_zero (hu : LipschitzWith L u) (hL : L < 1) (h0 : u 0 = 0) (s : ℝ)
    {y : V} (hy : y ≠ 0) : slice hu hL s y ≠ 0 := fun h ↦
  hy ((slice hu hL s).injective (h.trans (by rw [slice_apply, h0, smul_zero, add_zero])))

private theorem slice_symm_ne_zero (hu : LipschitzWith L u) (hL : L < 1) (h0 : u 0 = 0) (s : ℝ)
    {y : V} (hy : y ≠ 0) : (slice hu hL s).symm y ≠ 0 := fun h ↦
  hy (by rw [← (slice hu hL s).apply_symm_apply y, h, slice_apply, h0, smul_zero, add_zero])

/-- A slice commutes with dilations by nonnegative scalars when `u` does. -/
private theorem slice_smul (hu : LipschitzWith L u) (hL : L < 1)
    (hh : ∀ c : ℝ, 0 ≤ c → ∀ y, u (c • y) = c • u y) (s : ℝ) {c : ℝ} (hc : 0 ≤ c) (y : V) :
    slice hu hL s (c • y) = c • slice hu hL s y := by
  rw [slice_apply, slice_apply, hh c hc, smul_add, smul_comm]

private theorem slice_symm_smul (hu : LipschitzWith L u) (hL : L < 1)
    (hh : ∀ c : ℝ, 0 ≤ c → ∀ y, u (c • y) = c • u y) (s : ℝ) {c : ℝ} (hc : 0 ≤ c) (y : V) :
    (slice hu hL s).symm (c • y) = c • (slice hu hL s).symm y := by
  rw [Homeomorph.symm_apply_eq, slice_smul hu hL hh s hc, Homeomorph.apply_symm_apply]

end Interpolation

/-! ### The interpolation diffeotopy of the sphere -/

section Sphere

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- The pair `(s, x) ↦ (s, x)` of a parameter and a point of the sphere, read in `ℝ × E`. -/
private theorem contMDiff_prodMk_coe_sphere :
    ContMDiff (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ × E) k fun p : ℝ × sphere (0 : E) 1 ↦ (p.1, (p.2 : E)) :=
  contMDiff_fst.prodMk_space (contMDiff_coe_sphere.comp contMDiff_snd)

/-- A finite-dimensional sphere lives in a complete space. -/
private theorem completeSpace_of_fact (n : ℕ) [Fact (finrank ℝ E = n + 1)] : CompleteSpace E :=
  haveI := FiniteDimensional.of_fact_finrank_eq_succ (K := ℝ) (V := E) n
  FiniteDimensional.completeSpace ℝ E

/-- A `C^k` family indexed by `ℝ`, restricted to the times in `[0, 1]`. -/
private theorem contMDiff_comp_coe_Icc {g : ℝ × sphere (0 : E) 1 → sphere (0 : E) 1}
    (hg : ContMDiff (𝓘(ℝ).prod (𝓡 n)) (𝓡 n) k g) :
    ContMDiff ((𝓡∂ 1).prod (𝓡 n)) (𝓡 n) k fun p : I × sphere (0 : E) 1 ↦ g ((p.1 : ℝ), p.2) :=
  hg.comp ((contMDiff_subtypeVal_Icc.comp contMDiff_fst).prodMk contMDiff_snd)

variable [CompleteSpace E] {f : sphere (0 : E) 1 → sphere (0 : E) 1} {L : ℝ≥0}

/-- The slice at `s` of the interpolation, read on the sphere:
`x ↦ normalize (x + sinSqWeight s • (f x - x))`. -/
private def sphereSlice (hu : LipschitzWith L (sphereCone fun x ↦ (f x : E) - x)) (hL : L < 1)
    (s : ℝ) (x : sphere (0 : E) 1) : sphere (0 : E) 1 :=
  ⟨normalize (slice hu hL s x), mem_sphere_zero_iff_norm.2 (norm_normalize
    (slice_ne_zero hu hL (sphereCone_zero _) s (ne_zero_of_mem_unit_sphere x)))⟩

/-- The inverse of `sphereSlice`: the normalized inverse of the slice of `E`. -/
private def sphereSliceSymm (hu : LipschitzWith L (sphereCone fun x ↦ (f x : E) - x))
    (hL : L < 1) (s : ℝ) (y : sphere (0 : E) 1) : sphere (0 : E) 1 :=
  ⟨normalize ((slice hu hL s).symm y), mem_sphere_zero_iff_norm.2 (norm_normalize
    (slice_symm_ne_zero hu hL (sphereCone_zero _) s (ne_zero_of_mem_unit_sphere y)))⟩

private theorem coe_sphereSlice (hu : LipschitzWith L (sphereCone fun x ↦ (f x : E) - x))
    (hL : L < 1) (s : ℝ) (x : sphere (0 : E) 1) :
    (sphereSlice hu hL s x : E) = normalize (slice hu hL s x) :=
  (rfl)

private theorem coe_sphereSliceSymm (hu : LipschitzWith L (sphereCone fun x ↦ (f x : E) - x))
    (hL : L < 1) (s : ℝ) (y : sphere (0 : E) 1) :
    (sphereSliceSymm hu hL s y : E) = normalize ((slice hu hL s).symm y) :=
  (rfl)

private theorem sphereSliceSymm_sphereSlice
    (hu : LipschitzWith L (sphereCone fun x ↦ (f x : E) - x)) (hL : L < 1) (s : ℝ)
    (x : sphere (0 : E) 1) : sphereSliceSymm hu hL s (sphereSlice hu hL s x) = x := by
  refine Subtype.ext ?_
  rw [coe_sphereSliceSymm, coe_sphereSlice, normalize_apply_normalize fun c hc z ↦
      slice_symm_smul hu hL (fun c hc y ↦ sphereCone_smul hc y) s hc z,
    Homeomorph.symm_apply_apply, normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere x)]

private theorem sphereSlice_sphereSliceSymm
    (hu : LipschitzWith L (sphereCone fun x ↦ (f x : E) - x)) (hL : L < 1) (s : ℝ)
    (y : sphere (0 : E) 1) : sphereSlice hu hL s (sphereSliceSymm hu hL s y) = y := by
  refine Subtype.ext ?_
  rw [coe_sphereSlice, coe_sphereSliceSymm, normalize_apply_normalize fun c hc z ↦
      slice_smul hu hL (fun c hc y ↦ sphereCone_smul hc y) s hc z,
    Homeomorph.apply_symm_apply, normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere y)]

private theorem sphereSlice_zero (hu : LipschitzWith L (sphereCone fun x ↦ (f x : E) - x))
    (hL : L < 1) (x : sphere (0 : E) 1) : sphereSlice hu hL 0 x = x := by
  refine Subtype.ext ?_
  rw [coe_sphereSlice, slice_apply, sinSqWeight_zero, zero_smul, add_zero,
    normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere x)]

private theorem contMDiff_sphereSlice (hf : ContMDiff (𝓡 n) (𝓡 n) k f)
    (hu : LipschitzWith L (sphereCone fun x ↦ (f x : E) - x)) (hL : L < 1) :
    ContMDiff (𝓘(ℝ).prod (𝓡 n)) (𝓡 n) k fun p : ℝ × sphere (0 : E) 1 ↦
      sphereSlice hu hL p.1 p.2 := by
  refine ContMDiff.codRestrict_sphere (f := fun p : ℝ × sphere (0 : E) 1 ↦
    normalize (slice hu hL p.1 p.2)) (fun p ↦ ?_) _
  have hne : slice hu hL p.1 p.2 ≠ 0 :=
    slice_ne_zero hu hL (sphereCone_zero _) p.1 (ne_zero_of_mem_unit_sphere p.2)
  have hF : ContDiffAt ℝ k (fun q : ℝ × E ↦ normalize (slice hu hL q.1 q.2)) (p.1, (p.2 : E)) := by
    rw [slice_apply] at hne
    simp only [slice_apply]
    exact (contDiffAt_normalize hne).comp (p.1, (p.2 : E)) (contDiffAt_snd.add
      ((contDiff_sinSqWeight.contDiffAt.comp _ contDiffAt_fst).smul
        ((contDiffAt_sphereCone (ne_zero_of_mem_unit_sphere p.2)
          ((contMDiff_coe_sphere.comp hf).sub contMDiff_coe_sphere _)).comp (p.1, (p.2 : E))
          (contDiffAt_snd (p := (p.1, (p.2 : E)))))))
  exact hF.contMDiffAt.comp p (contMDiff_prodMk_coe_sphere (n := n) p)

private theorem contMDiff_sphereSliceSymm (hk : 1 ≤ k) (hf : ContMDiff (𝓡 n) (𝓡 n) k f)
    (hu : LipschitzWith L (sphereCone fun x ↦ (f x : E) - x)) (hL : L < 1) :
    ContMDiff (𝓘(ℝ).prod (𝓡 n)) (𝓡 n) k fun p : ℝ × sphere (0 : E) 1 ↦
      sphereSliceSymm hu hL p.1 p.2 := by
  refine ContMDiff.codRestrict_sphere (f := fun p : ℝ × sphere (0 : E) 1 ↦
    normalize ((slice hu hL p.1).symm p.2)) (fun p ↦ ?_) _
  have hne := slice_symm_ne_zero hu hL (sphereCone_zero _) p.1 (ne_zero_of_mem_unit_sphere p.2)
  -- The inverses of the slices are jointly `C^k` away from the origin, where the cone is `C^k`.
  have h₁ : ContDiffAt ℝ k (fun q : ℝ × E ↦ (slice hu hL q.1).symm q.2) (p.1, (p.2 : E)) :=
    hu.contDiffAt_idAddSmulHomeomorph_symm hL contDiff_sinSqWeight norm_sinSqWeight_le_one
      isOpen_compl_singleton (fun _ hy ↦ (contDiffAt_sphereCone hy
        ((contMDiff_coe_sphere.comp hf).sub contMDiff_coe_sphere _)).contDiffWithinAt) hk
      (q := (p.1, (p.2 : E))) hne
  have hF : ContDiffAt ℝ k (NormedSpace.normalize ∘ fun q : ℝ × E ↦ (slice hu hL q.1).symm q.2)
      (p.1, (p.2 : E)) :=
    (contDiffAt_normalize hne).comp (p.1, (p.2 : E)) h₁
  exact hF.contMDiffAt.comp p (contMDiff_prodMk_coe_sphere (n := n) p)

variable (f : Diff (𝓡 n) (sphere (0 : E) 1) k) {L : ℝ≥0} (hL : L < 1)
  (hlip : LipschitzWith L (sphereCone fun x ↦ (f x : E) - x)) (hk : 1 ≤ k)

omit [CompleteSpace E] in
/-- **Interpolation from the identity to a diffeomorphism of the sphere.** Let `f` be a `C^k`
diffeomorphism of the unit sphere, `1 ≤ k`, whose displacement `x ↦ f x - x` has an `L`-Lipschitz
cone `TauCeti.sphereCone`, `L < 1`. Then `(t, x) ↦ normalize (x + sin (π t / 2) ^ 2 • (f x - x))`
is a `C^k` diffeotopy of the sphere from the identity to `f`
(`TauCeti.coe_sphereInterpolationDiffeotopy_apply`, `TauCeti.sphereInterpolationDiffeotopy_final`).
-/
def sphereInterpolationDiffeotopy : Diffeotopy (𝓡 n) k (sphere (0 : E) 1) :=
  letI := completeSpace_of_fact (E := E) n
  { toDiffeomorph :=
      { toFun := fun p ↦ (p.1, sphereSlice hlip hL (p.1 : ℝ) p.2)
        invFun := fun p ↦ (p.1, sphereSliceSymm hlip hL (p.1 : ℝ) p.2)
        left_inv := fun p ↦ Prod.ext rfl (sphereSliceSymm_sphereSlice hlip hL _ p.2)
        right_inv := fun p ↦ Prod.ext rfl (sphereSlice_sphereSliceSymm hlip hL _ p.2)
        contMDiff_toFun := contMDiff_fst.prodMk
          (contMDiff_comp_coe_Icc (contMDiff_sphereSlice f.contMDiff hlip hL))
        contMDiff_invFun := contMDiff_fst.prodMk
          (contMDiff_comp_coe_Icc (contMDiff_sphereSliceSymm hk f.contMDiff hlip hL)) }
    fst_apply _ := rfl
    snd_apply_zero' x := sphereSlice_zero hlip hL x }

/-- At time `t`, the interpolation diffeotopy is the slice of the sphere at `t`. -/
private theorem sphereInterpolationDiffeotopy_apply_eq (p : I × sphere (0 : E) 1) :
    sphereInterpolationDiffeotopy f hL hlip hk p = sphereSlice hlip hL p.1 p.2 :=
  (rfl)

omit [CompleteSpace E] in
/-- At time `t`, the interpolation diffeotopy sends `x` to the normalization of
`x + sinSqWeight t • (f x - x)`, where `sinSqWeight t = sin (π t / 2) ^ 2`. -/
@[simp]
theorem coe_sphereInterpolationDiffeotopy_apply (p : I × sphere (0 : E) 1) :
    (sphereInterpolationDiffeotopy f hL hlip hk p : E) =
      normalize ((p.2 : E) + sinSqWeight p.1 • ((f p.2 : E) - p.2)) := by
  let := completeSpace_of_fact (E := E) n
  rw [sphereInterpolationDiffeotopy_apply_eq, coe_sphereSlice, slice_apply, sphereCone_coe]

/-- At time `t`, the inverse of the interpolation diffeotopy is the inverse slice of the sphere. -/
private theorem sphereInterpolationDiffeotopy_symm_apply_eq (p : I × sphere (0 : E) 1) :
    (sphereInterpolationDiffeotopy f hL hlip hk).symm p = sphereSliceSymm hlip hL p.1 p.2 := by
  -- The inverse of the diffeomorphism of `I × Sⁿ` is assembled from `sphereSliceSymm`.
  rw [Diffeotopy.symm_apply]
  rfl

/-- At time `t`, the inverse of the interpolation diffeotopy sends `y` to the normalization of the
solution `x` of `x + sinSqWeight t • u x = y`, where `u` is the cone over the displacement
`x ↦ f x - x` (`LipschitzWith.idAddSmulHomeomorph`). -/
theorem coe_sphereInterpolationDiffeotopy_symm_apply (p : I × sphere (0 : E) 1) :
    ((sphereInterpolationDiffeotopy f hL hlip hk).symm p : E) =
      normalize ((hlip.idAddSmulHomeomorph hL (sinSqWeight p.1)
        (norm_sinSqWeight_le_one _)).symm p.2) := by
  rw [sphereInterpolationDiffeotopy_symm_apply_eq, coe_sphereSliceSymm, slice]

omit [CompleteSpace E] in
/-- The interpolation diffeotopy ends at `f`. -/
@[simp]
theorem sphereInterpolationDiffeotopy_final :
    (sphereInterpolationDiffeotopy f hL hlip hk).final = f :=
  _root_.Diffeomorph.ext fun x ↦ Subtype.ext <| by
    let := completeSpace_of_fact (E := E) n
    rw [Diffeotopy.final_apply, sphereInterpolationDiffeotopy_apply_eq, coe_sphereSlice,
      slice_apply, Set.Icc.coe_one, sinSqWeight_one, sphereCone_coe]
    simp only [one_smul, add_sub_cancel]
    exact normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere _)

end Sphere

/-! ### The local isotopy lemma -/

section Local

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] [FiniteDimensional ℝ E]

/-- The punctured space `E \ {0}`, as an open subset of `E`. -/
private abbrev punctured (E : Type*) [NormedAddCommGroup E] : Opens E :=
  ⟨{0}ᶜ, isOpen_compl_singleton⟩

omit [InnerProductSpace ℝ E] [Fact (finrank ℝ E = n + 1)] [FiniteDimensional ℝ E] in
/-- The points of the annulus `1 / 2 ≤ ‖y‖` lie in the punctured space. -/
private theorem ne_zero_of_half_le_norm {y : E} (hy : 1 / 2 ≤ ‖y‖) : y ≠ 0 :=
  norm_pos_iff.1 (lt_of_lt_of_le (by norm_num) hy)

omit [FiniteDimensional ℝ E] in
/-- The displacement `y ↦ f (y / ‖y‖) - y / ‖y‖` of `f`, read on the punctured space through the
radial projection, as a `C^k` map. -/
private def displacement (f : Diff (𝓡 n) (sphere (0 : E) 1) k) :
    C^k⟮𝓘(ℝ, E), punctured E; 𝓘(ℝ, E), E⟯ :=
  ContMDiffMap.comp (ContMDiffMap.comp coeSphereMap f.toContMDiffMap - coeSphereMap)
    normalizeSphereMap

omit [FiniteDimensional ℝ E] in
private theorem displacement_apply (f : Diff (𝓡 n) (sphere (0 : E) 1) k) (y : punctured E) :
    displacement f y = (f (normalizeSphereMap (m := k) (n := n) y) : E) - normalize (y : E) := by
  rw [displacement, ContMDiffMap.comp_apply, ContMDiffMap.coe_sub, Pi.sub_apply,
    ContMDiffMap.comp_apply, coeSphereMap_apply, coeSphereMap_apply,
    Diffeomorph.coe_toContMDiffMap, coe_normalizeSphereMap_apply]

/-- The displacement depends continuously on `f`. -/
private theorem continuous_displacement :
    Continuous (displacement : Diff (𝓡 n) (sphere (0 : E) 1) k → _) := by
  have h₁ : Continuous fun g : C^k⟮𝓡 n, sphere (0 : E) 1; 𝓡 n, sphere (0 : E) 1⟯ ↦
      ContMDiffMap.comp coeSphereMap g :=
    ContMDiffMap.continuous_comp_manifoldWeakWhitney.comp (continuous_const.prodMk continuous_id)
  have h₂ : Continuous fun g : C^k⟮𝓡 n, sphere (0 : E) 1; 𝓘(ℝ, E), E⟯ ↦ g - coeSphereMap :=
    ContMDiffMap.continuous_sub_manifoldWeakWhitney.comp (continuous_id.prodMk continuous_const)
  have h₃ : Continuous fun g : C^k⟮𝓡 n, sphere (0 : E) 1; 𝓘(ℝ, E), E⟯ ↦
      ContMDiffMap.comp g (normalizeSphereMap (E := E)) :=
    ContMDiffMap.continuous_comp_manifoldWeakWhitney.comp (continuous_id.prodMk continuous_const)
  exact h₃.comp (h₂.comp (h₁.comp Diffeomorph.continuous_toContMDiffMap))

omit [FiniteDimensional ℝ E] in
/-- On the punctured space, the displacement is the `0`-homogeneous extension of `x ↦ f x - x`. -/
private theorem extend_displacement_eqOn (f : Diff (𝓡 n) (sphere (0 : E) 1) k) :
    EqOn (Function.extend Subtype.val (displacement f) fun _ ↦ (0 : E))
      (sphereExtend fun x ↦ (f x : E) - x) (punctured E) := fun y hy ↦ by
  have hy' : normalizeSphereMap (m := k) (n := n) ⟨y, hy⟩ =
      ⟨normalize y, mem_sphere_zero_iff_norm.2 (norm_normalize hy)⟩ :=
    Subtype.ext (coe_normalizeSphereMap_apply _)
  rw [Subtype.val_injective.extend_apply (displacement f) (fun _ ↦ (0 : E)) ⟨y, hy⟩,
    displacement_apply, sphereExtend_of_ne_zero _ hy, hy']

/-- Near the identity, the jets of order at most one of the displacement are small on the closed
annulus `1 / 2 ≤ ‖y‖ ≤ 1`, a compact subset of the punctured space. -/
private theorem eventually_forall_norm_iteratedFDerivWithin_lt (m : ℕ) (hm : (m : ℕ∞ω) ≤ k)
    {r : ℝ} (hr : 0 < r) :
    ∀ᶠ f in 𝓝 (1 : Diff (𝓡 n) (sphere (0 : E) 1) k), ∀ y : E, 1 / 2 ≤ ‖y‖ → ‖y‖ ≤ 1 →
      ‖iteratedFDerivWithin ℝ m (sphereExtend fun x ↦ (f x : E) - (x : E)) (punctured E) y‖ <
        r := by
  set A : Set (punctured E) := Subtype.val ⁻¹' (closedBall (0 : E) 1 ∩ {y | 1 / 2 ≤ ‖y‖})
  have hA : IsCompact A := IsInducing.subtypeVal.isCompact_preimage'
    ((isCompact_closedBall 0 1).inter_right (isClosed_le continuous_const continuous_norm))
    fun y hy ↦ ⟨⟨y, ne_zero_of_half_le_norm hy.2⟩, rfl⟩
  have hc : Continuous fun f : Diff (𝓡 n) (sphere (0 : E) 1) k ↦
      ContMDiffMap.openIteratedFDerivContinuousMap (punctured E) (displacement f) m hm :=
    ((continuous_apply (⟨m, hm⟩ : {m : ℕ // (m : ℕ∞ω) ≤ k})).comp
      ((ContMDiffMap.continuous_openWeakWhitneyJet (punctured E)).comp
        continuous_displacement)).congr fun f ↦
          ContMDiffMap.openWeakWhitneyJet_apply (punctured E) (displacement f) ⟨m, hm⟩
  -- The jet at a point of the punctured space is that of the `0`-homogeneous extension.
  have hjet (f : Diff (𝓡 n) (sphere (0 : E) 1) k) (y : punctured E) :
      ContMDiffMap.openIteratedFDerivContinuousMap (punctured E) (displacement f) m hm y =
        iteratedFDerivWithin ℝ m (sphereExtend fun x ↦ (f x : E) - (x : E)) (punctured E) y := by
    rw [ContMDiffMap.openIteratedFDerivContinuousMap_apply,
      iteratedFDerivWithin_congr (extend_displacement_eqOn f) y.property]
  -- The displacement of the identity vanishes, and so do its jets.
  have h0 : (fun x : sphere (0 : E) 1 ↦ ((1 : Diff (𝓡 n) (sphere (0 : E) 1) k) x : E) - x) = 0 :=
    funext fun x ↦ by rw [Diffeomorph.one_apply, sub_self, Pi.zero_apply]
  have h₁ : MapsTo (ContMDiffMap.openIteratedFDerivContinuousMap (punctured E) (displacement 1) m
      hm) A (ball 0 r) := fun y _ ↦ by
    rw [mem_ball_zero_iff, hjet, h0]
    simpa using hr
  filter_upwards [((ContinuousMap.isOpen_setOfPred_mapsTo hA isOpen_ball).preimage hc).mem_nhds
    h₁] with f hf y hy₁ hy₂
  have hyA : (⟨y, ne_zero_of_half_le_norm hy₁⟩ : punctured E) ∈ A :=
    ⟨mem_closedBall_zero_iff.2 hy₂, hy₁⟩
  simpa only [mem_ball_zero_iff, hjet] using hf hyA

/-- Near the identity, the displacement `x ↦ f x - x` is bounded by `1 / 8` and `1 / 4`-Lipschitz
on the sphere, so its cone is Lipschitz with constant `1 / 8 + 2 / 4 < 1`. -/
private theorem eventually_exists_lipschitzWith_sphereCone_sub (hk : 1 ≤ k) :
    ∀ᶠ f in 𝓝 (1 : Diff (𝓡 n) (sphere (0 : E) 1) k),
      ∃ L : ℝ≥0, L < 1 ∧ LipschitzWith L (sphereCone fun x ↦ (f x : E) - (x : E)) := by
  filter_upwards [eventually_forall_norm_iteratedFDerivWithin_lt (E := E) (n := n) 0 zero_le
    (r := 1 / 8) (by norm_num), eventually_forall_norm_iteratedFDerivWithin_lt (E := E) (n := n)
    1 (by exact_mod_cast hk) (r := 1 / 4) (by norm_num)] with f h₀ h₁
  set g := fun x : sphere (0 : E) 1 ↦ (f x : E) - x
  have hg : ContMDiff (𝓡 n) 𝓘(ℝ, E) k g := (contMDiff_coe_sphere.comp f.contMDiff).sub
    contMDiff_coe_sphere
  have hg₀ (x : sphere (0 : E) 1) : ‖g x‖ ≤ 1 / 8 := by
    have h := h₀ x (by norm_num [norm_eq_of_mem_sphere x]) (norm_eq_of_mem_sphere x).le
    rw [norm_iteratedFDerivWithin_zero, sphereExtend_coe] at h
    exact h.le
  have hd (y : E) (hy₁ : 1 / 2 ≤ ‖y‖) (hy₂ : ‖y‖ ≤ 1) : ‖fderiv ℝ (sphereExtend g) y‖ ≤ 1 / 4 := by
    have hy := ne_zero_of_half_le_norm hy₁
    have h := h₁ y hy₁ hy₂
    rw [norm_iteratedFDerivWithin_one _ ((punctured E).isOpen.uniqueDiffWithinAt hy),
      fderivWithin_of_isOpen (punctured E).isOpen hy] at h
    exact h.le
  -- Far apart points are handled by the bound on `g`, close ones by the mean value theorem.
  have hg₁ : LipschitzWith (1 / 4) g := LipschitzWith.of_dist_le_mul fun p q ↦ by
    rw [dist_eq_norm, Subtype.dist_eq, dist_eq_norm, NNReal.coe_div, NNReal.coe_one,
      NNReal.coe_ofNat]
    rcases le_or_gt ‖(p : E) - q‖ 1 with hpq | hpq
    · exact norm_sub_le_of_norm_fderiv_sphereExtend_le hk hg hd hpq
    · linarith [norm_sub_le (g p) (g q), hg₀ p, hg₀ q]
  refine ⟨1 / 8 + 2 * (1 / 4), ?_, lipschitzWith_sphereCone (fun x ↦ ?_) hg₁⟩
  · rw [← NNReal.coe_lt_coe]
    push_cast
    norm_num
  · push_cast
    exact hg₀ x

end Local

/-! ### Diffeotopy classes are path components -/

section Path

-- The weak Whitney topology of `Diff(Sⁿ)` needs the sphere to be compact, so `E` is
-- finite-dimensional as an instance.
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] [FiniteDimensional ℝ E]

/-- **The local isotopy lemma for spheres.** Every `C^k` diffeomorphism of the unit sphere close
enough to the identity in the weak Whitney topology, `1 ≤ k`, is the final diffeomorphism of a
`C^k` diffeotopy (`TauCeti.sphereInterpolationDiffeotopy`). -/
theorem eventually_exists_diffeotopy_final_eq (hk : 1 ≤ k) :
    ∀ᶠ f in 𝓝 (1 : Diff (𝓡 n) (sphere (0 : E) 1) k),
      ∃ Φ : Diffeotopy (𝓡 n) k (sphere (0 : E) 1), Φ.final = f :=
  (eventually_exists_lipschitzWith_sphereCone_sub hk).mono fun f ⟨_, hL, hlip⟩ ↦
    ⟨sphereInterpolationDiffeotopy f hL hlip hk, sphereInterpolationDiffeotopy_final f hL hlip hk⟩

/-- **The path components of `Diff(Sⁿ)` are its diffeotopy classes.** Two `C^k` diffeomorphisms
`f` and `g` of the unit sphere, `1 ≤ k`, are joined by a path in the weak Whitney topology exactly
when `g = f ∘ φ₁` for the final diffeomorphism `φ₁` of a `C^k` diffeotopy. -/
theorem joined_iff_exists_diffeotopy_mul_final_eq (hk : 1 ≤ k)
    {f g : Diff (𝓡 n) (sphere (0 : E) 1) k} :
    Joined f g ↔ ∃ Φ : Diffeotopy (𝓡 n) k (sphere (0 : E) 1), f * Φ.final = g := by
  refine ⟨fun hfg ↦ ?_, fun ⟨Φ, hΦ⟩ ↦ hΦ ▸ by
    simpa only [mul_one] using Φ.joined_one_final.map (continuous_const_mul f)⟩
  -- The final diffeomorphisms of diffeotopies form a subgroup which is a neighbourhood of the
  -- identity, so an open, hence closed, subgroup; it contains the path component of the identity.
  set H := (Diffeotopy.finalHom (𝓡 n) k (sphere (0 : E) 1)).range
  have hH : (H : Set (Diff (𝓡 n) (sphere (0 : E) 1) k)) ∈ 𝓝 1 :=
    (eventually_exists_diffeotopy_final_eq hk).mono fun h ⟨Φ, hΦ⟩ ↦
      MonoidHom.mem_range.2 ⟨Φ, (Diffeotopy.finalHom_apply Φ).trans hΦ⟩
  have hC : IsClopen (H : Set (Diff (𝓡 n) (sphere (0 : E) 1) k)) :=
    (⟨H, H.isOpen_of_mem_nhds hH⟩ : OpenSubgroup _).isClopen
  have h₁ : Joined 1 (f⁻¹ * g) := by
    simpa only [inv_mul_cancel] using hfg.map (continuous_const_mul f⁻¹)
  obtain ⟨Φ, hΦ⟩ := MonoidHom.mem_range.1 (hC.connectedComponent_subset H.one_mem
    (pathComponent_subset_component 1 (mem_pathComponent_iff.2 h₁)))
  exact ⟨Φ, by rw [← Diffeotopy.finalHom_apply, hΦ, mul_inv_cancel_left]⟩

end Path

end TauCeti
