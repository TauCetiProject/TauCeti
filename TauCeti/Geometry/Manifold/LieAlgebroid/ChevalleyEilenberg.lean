/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.Algebra.Lie.Cohomology.ChevalleyEilenberg
public import TauCeti.Geometry.Manifold.DeRham.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Basic
public import TauCeti.Geometry.Manifold.LieAlgebroid.Tangent
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Alternating
public import TauCeti.LinearAlgebra.Alternating.RestrictScalars
import TauCeti.Geometry.Manifold.DifferentialForm.VectorField
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# The Chevalley–Eilenberg complex of a Lie algebroid

Let `A : LieAlgebroid I F V` be a Lie algebroid on a finite-rank smooth real vector bundle `V → M`
over a finite-dimensional Hausdorff smooth manifold `M`. A smooth degree-`k` cochain on `A` is a
smooth section of the bundle `fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ` of continuous alternating forms on the
fibres of `V`.

By tensoriality (`ContMDiffSection.evalAlternatingEquiv`), smooth degree-`k` bundle sections
identify `C^∞(M)`-linearly with `C^∞(M)`-multilinear alternating maps on `A.Sections`
(`TauCeti.LieAlgebroid.cochainEquiv`). Restricting scalars from `C^∞(M)` to `ℝ`
(`AlternatingMap.restrictScalars`) embeds these into the `ℝ`-multilinear Lie-algebra cochains of
`A.Sections` with coefficients in `C^∞(M)` (`TauCeti.Algebra.Lie.Cohomology.ChevalleyEilenberg`).
Because the anchor and bracket of `A` satisfy the Lie–Rinehart Leibniz rules, both the Lie-algebra
action `⁅x, ·⁆` and the Chevalley–Eilenberg differential preserve `C^∞(M)`-multilinearity, equipping
the smooth bundle sections with:

* the Lie derivative `TauCeti.LieAlgebroid.lieDeriv` along smooth sections of `V`,
  intertwined with the Lie-algebra action via
  `TauCeti.LieAlgebroid.restrictScalars_cochainEquiv_lieDeriv`;
* the algebroid exterior derivative `TauCeti.LieAlgebroid.extDeriv` of degree `+1`, intertwined
  with `LieModule.Cohomology.d` via
  `TauCeti.LieAlgebroid.restrictScalars_cochainEquiv_extDeriv`, satisfying the explicit
  Chevalley–Eilenberg formula (`TauCeti.LieAlgebroid.evalAlternating_extDeriv_succ`) and
  `d_A ∘ d_A = 0` (`TauCeti.LieAlgebroid.extDeriv_extDeriv`);
* the Chevalley–Eilenberg cochain complex `TauCeti.LieAlgebroid.cochainComplex` in `ModuleCat ℝ`
  (with component identification `TauCeti.LieAlgebroid.cochainComplexXIso` and successor
  differential `TauCeti.LieAlgebroid.cochainComplex_d_succ`) and its cohomology
  `TauCeti.LieAlgebroid.cohomology`;
* the Cartan calculus identities relating `ContMDiffSection.interior`, `lieDeriv`, and
  `extDeriv`, together with degree transport commutation (`TauCeti.LieAlgebroid.extDeriv_cast`)
  and the graded derivation laws of `lieDeriv` and `extDeriv` across the fibrewise wedge product
  `ContMDiffSection.wedge` (`TauCeti.LieAlgebroid.lieDeriv_wedge`,
  `TauCeti.LieAlgebroid.extDeriv_wedge`);
* the comparison theorems `TauCeti.LieAlgebroid.tangent_extDeriv_toContMDiffSection`,
  `TauCeti.LieAlgebroid.tangentCochainComplexIso`, and
  `TauCeti.LieAlgebroid.tangentCohomologyIso` showing that specialising `A` to
  `TauCeti.LieAlgebroid.tangent` recovers the manifold exterior derivative `TauCeti.mextDerivₗ`
  on `SmoothForm I M ℝ k`, the de Rham complex `TauCeti.deRhamComplex I M`, and de Rham
  cohomology.

## References

* K. C. H. Mackenzie, *General theory of Lie groupoids and Lie algebroids*, London Math. Soc.
  Lecture Note Ser. 213, Cambridge University Press (2005), §3.3 and §7.1.
* M. Crainic and R. L. Fernandes, *Lectures on integrability of Lie brackets*, Geom. Topol.
  Monogr. 17 (2011), 1–107.
* G. S. Rinehart, *Differential forms on general commutative algebras*, Trans. Amer. Math. Soc.
  108 (1963), 195–222.
* C. Chevalley and S. Eilenberg, *Cohomology theory of Lie groups and Lie algebras*, Trans. Amer.
  Math. Soc. 63 (1948), 85–124.
-/

public section

noncomputable section

open Bundle CategoryTheory Function Manifold VectorField
open scoped ContDiff

namespace TauCeti.LieAlgebroid

section General

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I ∞ M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  (A : LieAlgebroid I F V)

local notation "Ω[" k "]" => Cₛ^∞⟮I; F [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ⟯

/-! ### Identification of bundle cochains with alternating maps on sections -/

/-- Smooth sections of `fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ` identify `C^∞(M)`-linearly with
`C^∞(M)`-multilinear alternating cochains on `A.Sections`. -/
def cochainEquiv (k : ℕ) :
    Ω[k] ≃ₗ[C^∞⟮I, M; ℝ⟯] (A.Sections [⋀^Fin k]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯) :=
  (ContMDiffSection.evalAlternatingEquiv I F ∞ V (Fin k)).trans
    (AlternatingMap.domLCongr C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ (Fin k) C^∞⟮I, M; ℝ⟯
      A.sectionsEquiv.symm)

@[simp]
theorem cochainEquiv_apply (k : ℕ) (φ : Ω[k]) (s : Fin k → A.Sections) :
    A.cochainEquiv k φ s = φ.evalAlternating (A.sectionsEquiv ∘ s) := by
  simp [cochainEquiv, Function.comp_def]

@[simp]
theorem evalAlternating_cochainEquiv_symm (k : ℕ)
    (Φ : A.Sections [⋀^Fin k]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯) (s : Fin k → Cₛ^∞⟮I; F, V⟯) :
    ((A.cochainEquiv k).symm Φ).evalAlternating s = Φ (A.sectionsEquiv.symm ∘ s) := by
  simp [cochainEquiv, Function.comp_def]

/-- `cochainEquiv` intertwines `ContMDiffSection.interior` with `AlternatingMap.curryLeft`. -/
@[simp]
theorem curryLeft_cochainEquiv {k : ℕ} (φ : Ω[k + 1]) (s : A.Sections) :
    (A.cochainEquiv (k + 1) φ).curryLeft s =
      A.cochainEquiv k (φ.interior (A.sectionsEquiv s)) := by
  simp [cochainEquiv, AlternatingMap.curryLeft_compLinearMap]

/-- Contracting `A.cochainEquiv (k + 1) φ` with `A.sectionsEquiv.symm a` corresponds to
`ContMDiffSection.interior`. -/
theorem curryLeft_cochainEquiv_symm {k : ℕ} (φ : Ω[k + 1]) (a : Cₛ^∞⟮I; F, V⟯) :
    (A.cochainEquiv (k + 1) φ).curryLeft (A.sectionsEquiv.symm a) =
      A.cochainEquiv k (φ.interior a) := by
  rw [A.curryLeft_cochainEquiv, A.sectionsEquiv.apply_symm_apply]

@[simp]
theorem cochainEquiv_zero_constOfIsEmptyEquiv (f : C^∞⟮I, M; ℝ⟯) :
    A.cochainEquiv 0 (ContMDiffSection.constOfIsEmptyEquiv I F ∞ V (Fin 0) f) =
      AlternatingMap.constOfIsEmpty C^∞⟮I, M; ℝ⟯ A.Sections (Fin 0) f := by
  ext s; simp [cochainEquiv_apply]

/-- Embed a smooth degree-`k` bundle cochain on `A` into the `ℝ`-multilinear Lie-algebra cochains
of `A.Sections` with coefficients in `C^∞⟮I, M; ℝ⟯`. -/
private def toLieCochain (k : ℕ) :
    Ω[k] →ₗ[ℝ] (A.Sections [⋀^Fin k]→ₗ[ℝ] C^∞⟮I, M; ℝ⟯) :=
  AlternatingMap.restrictScalarsₗ ℝ ℝ ∘ₗ (A.cochainEquiv k).toLinearMap.restrictScalars ℝ

private theorem toLieCochain_def (k : ℕ) (φ : Ω[k]) :
    A.toLieCochain k φ = (A.cochainEquiv k φ).restrictScalars ℝ := by
  simp [toLieCochain]

@[simp]
private theorem toLieCochain_apply (k : ℕ) (φ : Ω[k]) (s : Fin k → A.Sections) :
    A.toLieCochain k φ s = φ.evalAlternating (A.sectionsEquiv ∘ s) := by
  rw [toLieCochain_def, AlternatingMap.restrictScalars_apply, A.cochainEquiv_apply]

private theorem toLieCochain_injective (k : ℕ) : Injective (A.toLieCochain k) :=
  fun _ _ h ↦ (A.cochainEquiv k).injective
    ((AlternatingMap.restrictScalars_injective ℝ) (by simpa [toLieCochain_def] using h))

private theorem curryLeft_toLieCochain {k : ℕ} (φ : Ω[k + 1]) (a : Cₛ^∞⟮I; F, V⟯) :
    (A.toLieCochain (k + 1) φ).curryLeft (A.sectionsEquiv.symm a) =
      A.toLieCochain k (φ.interior a) := by
  rw [toLieCochain_def, AlternatingMap.curryLeft_restrictScalars, A.curryLeft_cochainEquiv_symm,
    toLieCochain_def]

/-! ### Lie derivative on bundle cochains -/

/-- The Lie-algebra action `⁅x, A.toLieCochain k φ⁆` remains `C^∞(M)`-linear in each argument:
the anchor derivative `⁅x, f⁆ * η w` on values cancels the `⁅x, f⁆ • w i` term from the
Lie–Rinehart Leibniz rule in slot `i`. -/
private theorem lie_toLieCochain_map_update_smul (k : ℕ) (x : A.Sections) (φ : Ω[k])
    (v : Fin k → A.Sections) (i : Fin k) (f : C^∞⟮I, M; ℝ⟯) (y : A.Sections) :
    ⁅x, A.toLieCochain k φ⁆ (update v i (f • y)) =
      f • ⁅x, A.toLieCochain k φ⁆ (update v i y) := by
  let η := A.cochainEquiv k φ
  let w : Fin k → A.Sections := update v i y
  have hw_eq : update v i (f • y) = update w i (f • w i) := by simp [w]
  have hself : update w i (w i) = w := update_eq_self i w
  have hterm_eq :
      η (update (update w i (f • w i)) i ⁅x, update w i (f • w i) i⁆) =
        f • η (update w i ⁅x, w i⁆) + ⁅x, f⁆ * η w := by
    rw [update_self, update_idem, LieRinehartRing.leibniz_smul_right, η.map_update_add,
      η.map_update_smul, η.map_update_smul, hself, smul_eq_mul, smul_eq_mul]
  have hterm_ne (j : Fin k) (hj : j ≠ i) :
      η (update (update w i (f • w i)) j ⁅x, update w i (f • w i) j⁆) =
        f • η (update w j ⁅x, w j⁆) := by
    rw [update_of_ne hj, update_comm hj.symm, η.map_update_smul]
    congr 2
    ext r; by_cases hr : r = i <;> simp [hr, hj.symm]
  have hsum :
      ∑ j : Fin k, η (update (update w i (f • w i)) j ⁅x, update w i (f • w i) j⁆) =
        f • (∑ j : Fin k, η (update w j ⁅x, w j⁆)) + ⁅x, f⁆ * η w := by
    rw [← Finset.insert_erase (Finset.mem_univ i), Finset.sum_insert (Finset.notMem_erase i _),
      Finset.sum_insert (Finset.notMem_erase i _), hterm_eq,
      Finset.sum_congr rfl fun j hj ↦ hterm_ne j (Finset.ne_of_mem_erase hj),
      ← Finset.smul_sum, smul_add]
    abel
  rw [toLieCochain_def, hw_eq, AlternatingMap.lie_apply, AlternatingMap.lie_apply]
  simp only [AlternatingMap.restrictScalars_apply]
  rw [η.map_update_smul, hself, smul_eq_mul, LieRinehartRing.leibniz_mul_right, hsum, smul_sub]
  abel

private def lieCochain (k : ℕ) (a : Cₛ^∞⟮I; F, V⟯) (φ : Ω[k]) :
    A.Sections [⋀^Fin k]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯ :=
  ⁅A.sectionsEquiv.symm a, A.toLieCochain k φ⁆.ofRestrictScalars C^∞⟮I, M; ℝ⟯
    (A.lie_toLieCochain_map_update_smul k (A.sectionsEquiv.symm a) φ)

/-- The Lie derivative `L_a` on smooth degree-`k` cochains of a Lie algebroid `A` along a smooth
section `a`, bundled as an `ℝ`-bilinear map. -/
def lieDeriv (k : ℕ) : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Ω[k] →ₗ[ℝ] Ω[k] where
  toFun a :=
    { toFun φ := (A.cochainEquiv k).symm (A.lieCochain k a φ)
      map_add' φ₁ φ₂ := A.toLieCochain_injective k <| by simp [toLieCochain_def, lieCochain]
      map_smul' c φ := A.toLieCochain_injective k <| by
        simpa only [RingHom.id_apply, toLieCochain_def, lieCochain,
          AlternatingMap.restrictScalars_ofRestrictScalars, LinearEquiv.apply_symm_apply, map_smul,
          AlternatingMap.restrictScalars_smul] using
          lie_smul c (A.sectionsEquiv.symm a) (A.toLieCochain k φ) }
  map_add' a₁ a₂ := LinearMap.ext fun φ ↦ A.toLieCochain_injective k <| by
    simpa only [LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk, toLieCochain_def, lieCochain,
      AlternatingMap.restrictScalars_ofRestrictScalars, LinearEquiv.apply_symm_apply, map_add,
      AlternatingMap.restrictScalars_add] using
      add_lie (A.sectionsEquiv.symm a₁) (A.sectionsEquiv.symm a₂) (A.toLieCochain k φ)
  map_smul' c a := LinearMap.ext fun φ ↦ A.toLieCochain_injective k <| by
    simpa only [RingHom.id_apply, LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk,
      toLieCochain_def, lieCochain, AlternatingMap.restrictScalars_ofRestrictScalars,
      LinearEquiv.apply_symm_apply, map_smul, AlternatingMap.restrictScalars_smul,
      LinearMapClass.map_smul_of_tower A.sectionsEquiv.symm c] using
      smul_lie c (A.sectionsEquiv.symm a) (A.toLieCochain k φ)

/-- `cochainEquiv` followed by `AlternatingMap.restrictScalars` intertwines `A.lieDeriv` with
the Lie-algebra action `⁅·, ·⁆` on `ℝ`-multilinear Lie-algebra cochains. -/
@[simp]
theorem restrictScalars_cochainEquiv_lieDeriv (k : ℕ) (a : Cₛ^∞⟮I; F, V⟯) (φ : Ω[k]) :
    (A.cochainEquiv k (A.lieDeriv k a φ)).restrictScalars ℝ =
      ⁅A.sectionsEquiv.symm a, (A.cochainEquiv k φ).restrictScalars ℝ⁆ := by
  simp only [lieDeriv, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply,
    lieCochain, AlternatingMap.restrictScalars_ofRestrictScalars, toLieCochain_def]

/-- `A.lieDeriv` commutes with degree transport. -/
theorem lieDeriv_cast {k l : ℕ} (h : k = l) (a : Cₛ^∞⟮I; F, V⟯) (φ : Ω[k]) :
    A.lieDeriv l a (LinearEquiv.cast (R := C^∞⟮I, M; ℝ⟯) (M := fun q : ℕ ↦ Ω[q]) h φ) =
      LinearEquiv.cast (R := C^∞⟮I, M; ℝ⟯) (M := fun q : ℕ ↦ Ω[q]) h (A.lieDeriv k a φ) := by
  subst h; rfl

/-- Evaluating `A.lieDeriv k a φ` on smooth sections differentiates along the anchor and subtracts
the algebroid brackets in each slot. -/
theorem evalAlternating_lieDeriv (k : ℕ) (a : Cₛ^∞⟮I; F, V⟯) (φ : Ω[k])
    (s : Fin k → Cₛ^∞⟮I; F, V⟯) :
    (A.lieDeriv k a φ).evalAlternating s =
      A.anchorDeriv a (φ.evalAlternating s) -
        ∑ i : Fin k, φ.evalAlternating (update s i (A.bracket a (s i))) := by
  let s' : Fin k → A.Sections := A.sectionsEquiv.symm ∘ s
  have hs' : A.sectionsEquiv ∘ s' = s := funext fun i ↦ A.sectionsEquiv.apply_symm_apply (s i)
  have hupd (i : Fin k) : A.sectionsEquiv ∘ update s' i ⁅A.sectionsEquiv.symm a, s' i⁆ =
      update s i (A.bracket a (s i)) := by
    funext j; by_cases hj : j = i <;> simp_all [s', sectionsEquiv_lie]
  have h := congr($(A.restrictScalars_cochainEquiv_lieDeriv k a φ) s')
  rw [AlternatingMap.restrictScalars_apply, A.cochainEquiv_apply, hs',
    AlternatingMap.lie_apply] at h
  simpa only [AlternatingMap.restrictScalars_apply, A.cochainEquiv_apply, hs', Sections.lie_def,
    A.sectionsEquiv.apply_symm_apply, hupd] using h

/-! ### The algebroid exterior derivative -/

/-- The Lie-algebra Chevalley–Eilenberg differential `LieModule.Cohomology.d` on
`A.toLieCochain k φ` preserves `C^∞(M)`-multilinearity: in degree `0` this is `C^∞(M)`-linearity
of the anchor, in positive degrees slots `j.succ` follow inductively from Cartan's formula
`ι_x d = L_x - d ι_x`, and slot `0` follows from slot `1` by alternation. -/
private theorem d_toLieCochain_map_update_smul :
    ∀ (k : ℕ) (φ : Ω[k]) (v : Fin (k + 1) → A.Sections)
      (i : Fin (k + 1)) (f : C^∞⟮I, M; ℝ⟯) (y : A.Sections),
      LieModule.Cohomology.d ℝ A.Sections C^∞⟮I, M; ℝ⟯ k (A.toLieCochain k φ)
          (update v i (f • y)) =
        f • LieModule.Cohomology.d ℝ A.Sections C^∞⟮I, M; ℝ⟯ k (A.toLieCochain k φ)
          (update v i y)
  | 0, φ, v, i, f, y => by
    obtain rfl : i = 0 := Fin.eq_zero i
    simp [LieModule.Cohomology.d_zero_apply]
  | k + 1, φ, v, i, f, y => by
    let D (η : Ω[k]) : A.Sections [⋀^Fin (k + 1)]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯ :=
      (LieModule.Cohomology.d ℝ A.Sections C^∞⟮I, M; ℝ⟯ k (A.toLieCochain k η)).ofRestrictScalars
        C^∞⟮I, M; ℝ⟯ (d_toLieCochain_map_update_smul k η)
    have hsucc (u : Fin (k + 2) → A.Sections) (j : Fin (k + 1)) (z : A.Sections) :
        LieModule.Cohomology.d ℝ A.Sections C^∞⟮I, M; ℝ⟯ (k + 1) (A.toLieCochain (k + 1) φ)
            (update u j.succ (f • z)) =
          f • LieModule.Cohomology.d ℝ A.Sections C^∞⟮I, M; ℝ⟯ (k + 1) (A.toLieCochain (k + 1) φ)
            (update u j.succ z) := by
      have hcons (w : A.Sections) :
          update u j.succ w = Matrix.vecCons (u 0) (update (Fin.tail u) j w) := by
        rw [Matrix.vecCons, Fin.cons_update, Fin.cons_self_tail]
      let a₀ : Cₛ^∞⟮I; F, V⟯ := A.sectionsEquiv (u 0)
      let ψ : A.Sections [⋀^Fin (k + 1)]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯ :=
        A.cochainEquiv (k + 1) (A.lieDeriv (k + 1) a₀ φ) - D (φ.interior a₀)
      have hψ (r : Fin (k + 1) → A.Sections) :
          LieModule.Cohomology.d ℝ A.Sections C^∞⟮I, M; ℝ⟯ (k + 1) (A.toLieCochain (k + 1) φ)
              (Matrix.vecCons (u 0) r) = ψ r := by
        have hu₀ : u 0 = A.sectionsEquiv.symm a₀ := (A.sectionsEquiv.symm_apply_apply (u 0)).symm
        rw [← AlternatingMap.curryLeft_apply_apply, LieModule.Cohomology.curryLeft_d_succ,
          sub_apply, hu₀, A.curryLeft_toLieCochain]
        simp only [toLieCochain_def]
        rw [← A.restrictScalars_cochainEquiv_lieDeriv]
        simp only [ψ, D, sub_apply, toLieCochain_def, AlternatingMap.restrictScalars_apply,
          AlternatingMap.ofRestrictScalars_apply]
      rw [hcons, hcons, hψ, hψ]
      exact ψ.map_update_smul (Fin.tail u) j f z
    refine Fin.cases ?_ (fun j ↦ hsucc v j y) i
    have h01 : (0 : Fin (k + 2)) ≠ 1 := Fin.zero_ne_one
    have hswap (z : A.Sections) :
        update v 0 z ∘ Equiv.swap (0 : Fin (k + 2)) 1 =
          update (v ∘ Equiv.swap 0 1) ((0 : Fin (k + 1)).succ) z := by
      rw [update_comp_equiv, Equiv.symm_swap, Equiv.swap_apply_left, Fin.succ_zero_eq_one]
    set F := LieModule.Cohomology.d ℝ A.Sections C^∞⟮I, M; ℝ⟯ (k + 1) (A.toLieCochain (k + 1) φ)
    apply neg_injective
    rw [← F.map_swap (update v 0 (f • y)) h01, hswap, hsucc (v ∘ Equiv.swap 0 1) 0 y, ← hswap,
      F.map_swap (update v 0 y) h01, smul_neg]

private def dCochain (k : ℕ) (φ : Ω[k]) :
    A.Sections [⋀^Fin (k + 1)]→ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯ :=
  (LieModule.Cohomology.d ℝ A.Sections C^∞⟮I, M; ℝ⟯ k (A.toLieCochain k φ)).ofRestrictScalars
    C^∞⟮I, M; ℝ⟯ (A.d_toLieCochain_map_update_smul k φ)

/-- The Chevalley–Eilenberg exterior derivative `d_A` of a Lie algebroid `A` in degree `k`,
bundled as an `ℝ`-linear map from degree-`k` to degree-`(k + 1)` smooth cochains. -/
def extDeriv (k : ℕ) : Ω[k] →ₗ[ℝ] Ω[k + 1] where
  toFun φ := (A.cochainEquiv (k + 1)).symm (A.dCochain k φ)
  map_add' φ₁ φ₂ := A.toLieCochain_injective (k + 1) <| by
    simp only [toLieCochain_def, dCochain, map_add, LinearEquiv.apply_symm_apply,
      AlternatingMap.restrictScalars_ofRestrictScalars]
  map_smul' c φ := A.toLieCochain_injective (k + 1) <| by
    simp only [RingHom.id_apply, toLieCochain_def, dCochain,
      LinearEquiv.apply_symm_apply, AlternatingMap.restrictScalars_ofRestrictScalars, map_smul]

/-- `cochainEquiv` followed by `AlternatingMap.restrictScalars` intertwines `A.extDeriv` with
the Lie-algebra Chevalley–Eilenberg differential `LieModule.Cohomology.d`. -/
@[simp]
theorem restrictScalars_cochainEquiv_extDeriv (k : ℕ) (φ : Ω[k]) :
    (A.cochainEquiv (k + 1) (A.extDeriv k φ)).restrictScalars ℝ =
      LieModule.Cohomology.d ℝ A.Sections C^∞⟮I, M; ℝ⟯ k
        ((A.cochainEquiv k φ).restrictScalars ℝ) := by
  simp only [extDeriv, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply,
    dCochain, AlternatingMap.restrictScalars_ofRestrictScalars, toLieCochain_def]

/-- `A.extDeriv` commutes with degree transport. -/
theorem extDeriv_cast {k l : ℕ} (h : k = l) (φ : Ω[k]) :
    A.extDeriv l (LinearEquiv.cast (R := C^∞⟮I, M; ℝ⟯) (M := fun q : ℕ ↦ Ω[q]) h φ) =
      LinearEquiv.cast (R := C^∞⟮I, M; ℝ⟯) (M := fun q : ℕ ↦ Ω[q]) (congrArg (· + 1) h)
        (A.extDeriv k φ) := by
  subst h; rfl

/-- In degree zero, `d_A φ` evaluated on a section `s 0` differentiates `φ` along the anchor of
`s 0`. -/
@[simp]
theorem evalAlternating_extDeriv_zero (φ : Ω[0]) (s : Fin 1 → Cₛ^∞⟮I; F, V⟯) :
    (A.extDeriv 0 φ).evalAlternating s = A.anchorDeriv (s 0) (φ.evalAlternating ![]) := by
  let s' : Fin 1 → A.Sections := A.sectionsEquiv.symm ∘ s
  have hs' : A.sectionsEquiv ∘ s' = s := funext fun i ↦ A.sectionsEquiv.apply_symm_apply (s i)
  have h0 : A.sectionsEquiv ∘ ![] = ![] := Subsingleton.elim _ _
  have h := congr($(A.restrictScalars_cochainEquiv_extDeriv 0 φ) s')
  rw [AlternatingMap.restrictScalars_apply, A.cochainEquiv_apply, hs',
    LieModule.Cohomology.d_zero_apply] at h
  simpa only [AlternatingMap.restrictScalars_apply, A.cochainEquiv_apply, Sections.lie_def, h0, s',
    Function.comp_apply, A.sectionsEquiv.apply_symm_apply] using h

/-- Evaluating `d_A` of the degree-zero section attached to `f` on `a` gives `A.anchorDeriv a f`. -/
theorem evalAlternating_extDeriv_zero_constOfIsEmptyEquiv
    (f : C^∞⟮I, M; ℝ⟯) (a : Cₛ^∞⟮I; F, V⟯) :
    (A.extDeriv 0 (ContMDiffSection.constOfIsEmptyEquiv I F ∞ V (Fin 0) f)).evalAlternating ![a] =
      A.anchorDeriv a f := by simp

/-- Pointwise formula for the degree-zero algebroid exterior derivative:
`(d_A φ)_x (v) = mvfderiv I (y ↦ φ_y(0)) x (ρ_x(v_0))`. -/
@[simp]
theorem extDeriv_zero_apply (φ : Ω[0]) (x : M) (v : Fin 1 → V x) :
    A.extDeriv 0 φ x v = mvfderiv I (fun y ↦ φ y 0) x (A.anchor x (v 0)) := by
  obtain ⟨a, ha⟩ := ContMDiffSection.exists_apply_eq (I := I) (F := F) ∞ x (v 0)
  have hv : v = fun i ↦ (![a] : Fin 1 → Cₛ^∞⟮I; F, V⟯) i x :=
    funext fun i ↦ Fin.eq_zero i ▸ ha.symm
  have hφ0 : ⇑(φ.evalAlternating ![]) = fun y ↦ φ y 0 :=
    funext fun y ↦ (ContMDiffSection.evalAlternating_apply ..).trans
      (congrArg (φ y) (Subsingleton.elim _ _))
  conv_lhs => rw [hv]
  rw [← ContMDiffSection.evalAlternating_apply, A.evalAlternating_extDeriv_zero,
    anchorDeriv_apply, hφ0, Matrix.cons_val_zero, ha]

/-- **The Chevalley–Eilenberg formula** for a Lie algebroid in arbitrary positive degree:
`(d_A φ)(s₀, …, sₖ₊₁) = ∑ i, (-1)^i ρ(sᵢ)(φ(…, ŝᵢ, …))`
`  + ∑_{i ≤ j} (-1)^(i + j + 1) φ([s_{i.castSucc}, s_{j.succ}], …)`. -/
theorem evalAlternating_extDeriv_succ {k : ℕ} (φ : Ω[k + 1]) (s : Fin (k + 2) → Cₛ^∞⟮I; F, V⟯) :
    (A.extDeriv (k + 1) φ).evalAlternating s =
      ∑ i : Fin (k + 2),
          (-1 : ℤ) ^ (i : ℕ) • A.anchorDeriv (s i) (φ.evalAlternating (i.removeNth s)) +
        ∑ i : Fin (k + 1), ∑ j ≥ i, (-1 : ℤ) ^ (i + j + 1 : ℕ) •
          φ.evalAlternating
            (Matrix.vecCons (A.bracket (s i.castSucc) (s j.succ))
              (j.removeNth (i.castSucc.removeNth s))) := by
  let s' : Fin (k + 2) → A.Sections := A.sectionsEquiv.symm ∘ s
  have hs' : A.sectionsEquiv ∘ s' = s := funext fun r ↦ A.sectionsEquiv.apply_symm_apply (s r)
  have hrem (i : Fin (k + 2)) : A.sectionsEquiv ∘ i.removeNth s' = i.removeNth s := by
    funext r; simp [s', Fin.removeNth]
  have hcons (i j : Fin (k + 1)) :
      A.sectionsEquiv ∘
          Matrix.vecCons ⁅s' i.castSucc, s' j.succ⁆ (j.removeNth (i.castSucc.removeNth s')) =
        Matrix.vecCons (A.bracket (s i.castSucc) (s j.succ))
          (j.removeNth (i.castSucc.removeNth s)) := by
    funext r; refine Fin.cases ?_ (fun r ↦ ?_) r <;> simp [s', Fin.removeNth, sectionsEquiv_lie]
  have h := congr($(A.restrictScalars_cochainEquiv_extDeriv (k + 1) φ) s')
  rw [AlternatingMap.restrictScalars_apply, A.cochainEquiv_apply, hs',
    LieModule.Cohomology.d_succ_apply] at h
  simp only [AlternatingMap.restrictScalars_apply, A.cochainEquiv_apply, Sections.lie_def, hrem,
    hcons] at h
  simpa only [s', Function.comp_apply, A.sectionsEquiv.apply_symm_apply] using h

/-- The degree-`1` Chevalley–Eilenberg formula for a Lie algebroid:
`(d_A φ)(a, b) = ρ(a)(φ(b)) - ρ(b)(φ(a)) - φ([a, b])`. -/
theorem evalAlternating_extDeriv_one (φ : Ω[1]) (a b : Cₛ^∞⟮I; F, V⟯) :
    (A.extDeriv 1 φ).evalAlternating ![a, b] =
      A.anchorDeriv a (φ.evalAlternating ![b]) -
        A.anchorDeriv b (φ.evalAlternating ![a]) -
        φ.evalAlternating ![A.bracket a b] := by
  have hrem0 : (0 : Fin 2).removeNth ![a, b] = ![b] := funext fun i ↦ Fin.eq_zero i ▸ rfl
  have hrem1 : (1 : Fin 2).removeNth ![a, b] = ![a] := funext fun i ↦ Fin.eq_zero i ▸ rfl
  have hIci : Finset.Ici (0 : Fin 1) = Finset.univ :=
    Finset.eq_univ_iff_forall.mpr fun i ↦ by simp [Fin.eq_zero i]
  rw [A.evalAlternating_extDeriv_succ (k := 0) φ ![a, b], Fin.sum_univ_two, Fin.sum_univ_one,
    hIci, Fin.sum_univ_one]
  simp only [Fin.isValue, Fin.val_zero, pow_zero, Matrix.cons_val_zero, hrem0,
    Fin.val_one, pow_one, neg_smul, one_smul, Matrix.cons_val_one, hrem1,
    Fin.castSucc_zero, zero_add]
  abel

/-- The exterior derivative of a Lie algebroid squares to zero. -/
@[simp]
theorem extDeriv_extDeriv (k : ℕ) (φ : Ω[k]) : A.extDeriv (k + 1) (A.extDeriv k φ) = 0 :=
  A.toLieCochain_injective (k + 2) (by simp [toLieCochain_def])

/-- The exterior derivative of a Lie algebroid squares to zero as a composite of `ℝ`-linear maps. -/
theorem extDeriv_comp_extDeriv (k : ℕ) : A.extDeriv (k + 1) ∘ₗ A.extDeriv k = 0 :=
  LinearMap.ext (A.extDeriv_extDeriv k)

/-! ### The Chevalley–Eilenberg cochain complex and cohomology -/

/-- The Chevalley–Eilenberg cochain complex `(Ω^•(A), d_A)` of a Lie algebroid `A` in
`ModuleCat ℝ`, with degree-`k` cochains the smooth sections of `fun x ↦ V x [⋀^Fin k]→L[ℝ] ℝ`. -/
def cochainComplex : CochainComplex (ModuleCat ℝ) ℕ :=
  CochainComplex.of (fun k ↦ ModuleCat.of ℝ Ω[k]) (fun k ↦ ModuleCat.ofHom (A.extDeriv k))
    fun k ↦ by rw [← ModuleCat.ofHom_comp, A.extDeriv_comp_extDeriv, ModuleCat.ofHom_zero]

/-- The canonical identification of the degree-`k` object of `A.cochainComplex` with the
`ℝ`-module of smooth degree-`k` cochains. -/
def cochainComplexXIso (k : ℕ) : A.cochainComplex.X k ≅ ModuleCat.of ℝ Ω[k] :=
  by unfold cochainComplex; exact Iso.refl _

/-- Under `cochainComplexXIso`, the successor differential of `A.cochainComplex` is
`A.extDeriv k`. -/
@[reassoc]
theorem cochainComplex_d_succ (k : ℕ) :
    A.cochainComplex.d k (k + 1) ≫ (A.cochainComplexXIso (k + 1)).hom =
      (A.cochainComplexXIso k).hom ≫ ModuleCat.ofHom (A.extDeriv k) := by
  dsimp +instances [cochainComplexXIso, cochainComplex]; simp

/-- Evaluating the successor differential of `A.cochainComplex` on an element via
`cochainComplexXIso`. -/
theorem cochainComplex_d_succ_apply (k : ℕ) (φ : A.cochainComplex.X k) :
    A.cochainComplex.d k (k + 1) φ =
      (A.cochainComplexXIso (k + 1)).inv
        (A.extDeriv k ((A.cochainComplexXIso k).hom φ)) := by
  rw [(Iso.eq_comp_inv _).mpr (A.cochainComplex_d_succ k), ModuleCat.comp_apply,
    ModuleCat.comp_apply, ConcreteCategory.hom_ofHom]

/-- The `k`-th Lie algebroid cohomology `H^k(A)` of `A`. -/
abbrev cohomology (k : ℕ) : ModuleCat ℝ :=
  A.cochainComplex.homology k

/-! ### Cartan calculus on bundle cochains -/

/-- Cartan's formula in degree zero: `ι_a (d_A φ) = L_a φ`. -/
@[simp]
theorem interior_extDeriv_zero (φ : Ω[0]) (a : Cₛ^∞⟮I; F, V⟯) :
    (A.extDeriv 0 φ).interior a = A.lieDeriv 0 a φ :=
  A.toLieCochain_injective 0 <| by
    simp only [toLieCochain_def]
    rw [← A.curryLeft_cochainEquiv_symm, ← AlternatingMap.curryLeft_restrictScalars,
      A.restrictScalars_cochainEquiv_extDeriv, LieModule.Cohomology.curryLeft_d_zero,
      A.restrictScalars_cochainEquiv_lieDeriv]

/-- **Cartan's magic formula** `ι_a (d_A φ) = L_a φ - d_A (ι_a φ)` on Lie algebroid cochains. -/
@[simp]
theorem interior_extDeriv_succ {k : ℕ} (φ : Ω[k + 1]) (a : Cₛ^∞⟮I; F, V⟯) :
    (A.extDeriv (k + 1) φ).interior a =
      A.lieDeriv (k + 1) a φ - A.extDeriv k (φ.interior a) :=
  A.toLieCochain_injective (k + 1) <| by
    simp only [toLieCochain_def]
    rw [← A.curryLeft_cochainEquiv_symm, ← AlternatingMap.curryLeft_restrictScalars,
      A.restrictScalars_cochainEquiv_extDeriv, LieModule.Cohomology.curryLeft_d_succ,
      map_sub, AlternatingMap.restrictScalars_sub, A.restrictScalars_cochainEquiv_lieDeriv,
      A.restrictScalars_cochainEquiv_extDeriv, AlternatingMap.curryLeft_restrictScalars,
      A.curryLeft_cochainEquiv_symm]

/-- Cartan's magic formula solved for the Lie derivative: `L_a φ = ι_a (d_A φ) + d_A (ι_a φ)`. -/
theorem lieDeriv_eq_interior_extDeriv_add_extDeriv_interior {k : ℕ}
    (a : Cₛ^∞⟮I; F, V⟯) (φ : Ω[k + 1]) :
    A.lieDeriv (k + 1) a φ =
      (A.extDeriv (k + 1) φ).interior a + A.extDeriv k (φ.interior a) := by
  rw [A.interior_extDeriv_succ, sub_add_cancel]

/-- Scaling the differentiating section by a smooth function `f` in degree `0` scales `L_a φ`. -/
@[simp]
theorem lieDeriv_smul_left_zero (f : C^∞⟮I, M; ℝ⟯) (a : Cₛ^∞⟮I; F, V⟯) (φ : Ω[0]) :
    A.lieDeriv 0 (f • a) φ = f • A.lieDeriv 0 a φ := by
  rw [← A.interior_extDeriv_zero, ContMDiffSection.interior_smul_right,
    A.interior_extDeriv_zero]

/-- Scaling the differentiating section by a smooth function `f` in positive degree satisfies
`L_{f • a} φ = f • ι_a (d_A φ) + d_A (f • ι_a φ)`. -/
theorem lieDeriv_smul_left_succ {k : ℕ} (f : C^∞⟮I, M; ℝ⟯) (a : Cₛ^∞⟮I; F, V⟯) (φ : Ω[k + 1]) :
    A.lieDeriv (k + 1) (f • a) φ =
      f • (A.extDeriv (k + 1) φ).interior a + A.extDeriv k (f • φ.interior a) := by
  rw [A.lieDeriv_eq_interior_extDeriv_add_extDeriv_interior,
    ContMDiffSection.interior_smul_right, ContMDiffSection.interior_smul_right]

/-- Leibniz rule for `A.lieDeriv` under scalar multiplication of a cochain by a smooth function:
`L_a (f • φ) = (ρ(a) f) • φ + f • L_a φ`. -/
@[simp]
theorem lieDeriv_smul_right (k : ℕ) (a : Cₛ^∞⟮I; F, V⟯) (f : C^∞⟮I, M; ℝ⟯) (φ : Ω[k]) :
    A.lieDeriv k a (f • φ) = A.anchorDeriv a f • φ + f • A.lieDeriv k a φ := by
  refine ContMDiffSection.eq_of_evalAlternating_eq <| AlternatingMap.ext fun s ↦ ?_
  simp only [A.evalAlternating_lieDeriv, ContMDiffSection.evalAlternating_add,
    ContMDiffSection.evalAlternating_smul, add_apply, smul_apply,
    smul_eq_mul, A.anchorDeriv_mul_right, ← Finset.mul_sum]
  ring

/-- Commutation of the Lie derivative with interior product:
`ι_b (L_a φ) = L_a (ι_b φ) - ι_{[a, b]} φ`. -/
theorem interior_lieDeriv {k : ℕ} (a b : Cₛ^∞⟮I; F, V⟯) (φ : Ω[k + 1]) :
    (A.lieDeriv (k + 1) a φ).interior b =
      A.lieDeriv k a (φ.interior b) - φ.interior (A.bracket a b) :=
  A.toLieCochain_injective k <| by
    have hbr : ⁅A.sectionsEquiv.symm a, A.sectionsEquiv.symm b⁆ =
        A.sectionsEquiv.symm (A.bracket a b) :=
      A.sectionsEquiv.injective (by simp [sectionsEquiv_lie])
    simp only [toLieCochain_def]
    rw [← A.curryLeft_cochainEquiv_symm, ← AlternatingMap.curryLeft_restrictScalars,
      A.restrictScalars_cochainEquiv_lieDeriv, AlternatingMap.curryLeft_lie, map_sub,
      AlternatingMap.restrictScalars_sub, A.restrictScalars_cochainEquiv_lieDeriv,
      AlternatingMap.curryLeft_restrictScalars, A.curryLeft_cochainEquiv_symm, hbr,
      AlternatingMap.curryLeft_restrictScalars, A.curryLeft_cochainEquiv_symm]

/-- The Lie derivative commutes with the exterior derivative: `L_a (d_A φ) = d_A (L_a φ)`. -/
@[simp]
theorem lieDeriv_extDeriv (k : ℕ) (a : Cₛ^∞⟮I; F, V⟯) (φ : Ω[k]) :
    A.lieDeriv (k + 1) a (A.extDeriv k φ) = A.extDeriv k (A.lieDeriv k a φ) :=
  A.toLieCochain_injective (k + 1) <| by
    simp only [toLieCochain_def, A.restrictScalars_cochainEquiv_lieDeriv,
      A.restrictScalars_cochainEquiv_extDeriv, LieModule.Cohomology.lie_d]

/-- The Lie derivative is a Lie algebra representation: `L_{[a, b]} = [L_a, L_b]`. -/
theorem lieDeriv_bracket (k : ℕ) (a b : Cₛ^∞⟮I; F, V⟯) (φ : Ω[k]) :
    A.lieDeriv k (A.bracket a b) φ =
      A.lieDeriv k a (A.lieDeriv k b φ) - A.lieDeriv k b (A.lieDeriv k a φ) :=
  A.toLieCochain_injective k <| by
    have hbr : A.sectionsEquiv.symm (A.bracket a b) =
        ⁅A.sectionsEquiv.symm a, A.sectionsEquiv.symm b⁆ :=
      A.sectionsEquiv.injective (by simp [sectionsEquiv_lie])
    simp only [toLieCochain_def, map_sub, A.restrictScalars_cochainEquiv_lieDeriv, hbr]
    exact lie_lie (A.sectionsEquiv.symm a) (A.sectionsEquiv.symm b)
      ((A.cochainEquiv k φ).restrictScalars ℝ)

/-! ### Graded derivations on the fibrewise wedge product -/

omit [FiniteDimensional ℝ E] [T2Space M] [FiniteDimensional ℝ F]
  [ContMDiffVectorBundle ∞ F V I] in
/-- Reindexing the Lie-bracket slot sum along `σ : Equiv.Perm (Fin (k + l))` splits it into the
slots of `φ` and the slots of `ψ`. -/
private theorem sum_update_wedge_split {k l : ℕ} (a : Cₛ^∞⟮I; F, V⟯) (φ : Ω[k]) (ψ : Ω[l])
    (s : Fin (k + l) → Cₛ^∞⟮I; F, V⟯) (σ : Equiv.Perm (Fin (k + l))) :
    (∑ r : Fin (k + l),
        φ.evalAlternating (fun i ↦ update s r (A.bracket a (s r)) (σ (Fin.castAdd l i))) *
          ψ.evalAlternating (fun j ↦ update s r (A.bracket a (s r)) (σ (Fin.natAdd k j)))) =
      (∑ i : Fin k,
          φ.evalAlternating (update (fun i' ↦ s (σ (Fin.castAdd l i'))) i
            (A.bracket a (s (σ (Fin.castAdd l i))))) *
            ψ.evalAlternating (fun j ↦ s (σ (Fin.natAdd k j)))) +
        ∑ j : Fin l,
          φ.evalAlternating (fun i ↦ s (σ (Fin.castAdd l i))) *
            ψ.evalAlternating (update (fun j' ↦ s (σ (Fin.natAdd k j'))) j
              (A.bracket a (s (σ (Fin.natAdd k j))))) := by
  have hdisj (i : Fin k) (j : Fin l) : σ (Fin.castAdd l i) ≠ σ (Fin.natAdd k j) :=
    σ.injective.ne fun heq ↦ by have := congrArg Fin.val heq; simp at this; omega
  rw [← Equiv.sum_comp σ, Fin.sum_univ_add]
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ congrArg₂ (· * ·)
      (congrArg φ.evalAlternating <|
        update_comp_eq_of_injective s (σ.injective.comp (Fin.castAdd_injective k l)) i _)
      (congrArg ψ.evalAlternating <|
        update_comp_eq_of_forall_ne s (f := σ ∘ Fin.natAdd k) _ fun j ↦ (hdisj i j).symm)
  · refine Finset.sum_congr rfl fun j _ ↦ congrArg₂ (· * ·)
      (congrArg φ.evalAlternating <|
        update_comp_eq_of_forall_ne s (f := σ ∘ Fin.castAdd l) _ fun i ↦ hdisj i j)
      (congrArg ψ.evalAlternating <|
        update_comp_eq_of_injective s (σ.injective.comp (Fin.natAdd_injective l k)) j _)

/-- The Lie derivative is an even derivation of the fibrewise wedge product:
`L_a (φ ∧ ψ) = L_a φ ∧ ψ + φ ∧ L_a ψ`. -/
theorem lieDeriv_wedge {k l : ℕ} (a : Cₛ^∞⟮I; F, V⟯) (φ : Ω[k]) (ψ : Ω[l]) :
    A.lieDeriv (k + l) a (φ.wedge ψ) =
      (A.lieDeriv k a φ).wedge ψ + φ.wedge (A.lieDeriv l a ψ) := by
  refine ContMDiffSection.eq_of_evalAlternating_eq <| AlternatingMap.ext fun s ↦ ?_
  -- Expand both sides via `evalAlternating_wedge_apply` and reindex the slot sum along `σ`.
  let D : C^∞⟮I, M; ℝ⟯ →+ C^∞⟮I, M; ℝ⟯ :=
    AddMonoidHom.mk' (A.anchorDeriv a) (A.anchorDeriv_add_right a)
  have hD (f : C^∞⟮I, M; ℝ⟯) : A.anchorDeriv a f = D f := rfl
  rw [A.evalAlternating_lieDeriv, ContMDiffSection.evalAlternating_add, add_apply]
  simp only [ContMDiffSection.evalAlternating_wedge_apply]
  rw [A.anchorDeriv_const_smul_right, hD, map_sum, ← Finset.smul_sum, Finset.sum_comm]
  simp only [Units.smul_def, map_zsmul]
  simp only [← hD, ← Finset.smul_sum, A.sum_update_wedge_split a φ ψ s]
  rw [← smul_sub, ← smul_add, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [← zsmul_sub, ← zsmul_add]
  congr 1
  rw [A.evalAlternating_lieDeriv, A.evalAlternating_lieDeriv, A.anchorDeriv_mul_right,
    sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum]
  ring

/-- Pointwise Cartan expansion of `d_A η` in positive degree along a section `a` with
`a x = v 0`. -/
private theorem extDeriv_succ_apply_eq_sub {m : ℕ} (η : Ω[m + 1])
    {a : Cₛ^∞⟮I; F, V⟯} {x : M} {v : Fin (m + 2) → V x} (ha : a x = v 0) :
    A.extDeriv (m + 1) η x v =
      A.lieDeriv (m + 1) a η x (Fin.tail v) -
        A.extDeriv m (η.interior a) x (Fin.tail v) := by
  rw [ContMDiffSection.apply_eq_interior_tail _ ha, A.interior_extDeriv_succ]; simp

/-- Pointwise expansion of the derivation law `L_a (φ ∧ ψ) = L_a φ ∧ ψ + φ ∧ L_a ψ`. -/
private theorem lieDeriv_wedge_apply {k l : ℕ} (a : Cₛ^∞⟮I; F, V⟯) (φ : Ω[k]) (ψ : Ω[l])
    (x : M) (u : Fin (k + l) → V x) :
    A.lieDeriv (k + l) a (φ.wedge ψ) x u =
      (A.lieDeriv k a φ).wedge ψ x u + φ.wedge (A.lieDeriv l a ψ) x u := by
  rw [A.lieDeriv_wedge]; simp

/-- Pointwise Cartan expansion of `d_A (φ ∧ ψ)` when the right factor has positive degree. -/
private theorem extDeriv_wedge_succ_right_apply {k l : ℕ} (φ : Ω[k]) (ψ : Ω[l + 1])
    {a : Cₛ^∞⟮I; F, V⟯} {x : M} {v : Fin (k + (l + 1) + 1) → V x} (ha : a x = v 0) :
    A.extDeriv (k + (l + 1)) (φ.wedge ψ) x v =
      (A.lieDeriv k a φ).wedge ψ x (Fin.tail v) +
        φ.wedge (A.lieDeriv (l + 1) a ψ) x (Fin.tail v) -
        A.extDeriv (k + l) ((φ.wedge ψ).interior a) x (Fin.tail v) :=
  (A.extDeriv_succ_apply_eq_sub (m := k + l) (φ.wedge ψ) ha).trans <|
    congrArg (· - _) (A.lieDeriv_wedge_apply a φ ψ x (Fin.tail v))

/-- Pointwise Cartan expansion of `(ι_a (d_A φ)) ∧ ψ` in positive degree `k + 1`. -/
private theorem interior_extDeriv_succ_wedge_left {k l : ℕ}
    (φ : Ω[k + 1]) (ψ : Ω[l]) (a : Cₛ^∞⟮I; F, V⟯) (x : M) (u : Fin (k + 1 + l) → V x) :
    ((A.extDeriv (k + 1) φ).interior a).wedge ψ x u =
      (A.lieDeriv (k + 1) a φ).wedge ψ x u -
        (A.extDeriv k (φ.interior a)).wedge ψ x u := by
  rw [A.interior_extDeriv_succ, ContMDiffSection.wedge_sub_left]; simp

/-- Pointwise Cartan expansion of `φ ∧ (ι_a (d_A ψ))` in positive degree `l + 1`. -/
private theorem wedge_interior_extDeriv_succ_right {k l : ℕ}
    (φ : Ω[k]) (ψ : Ω[l + 1]) (a : Cₛ^∞⟮I; F, V⟯) (x : M) (u : Fin (k + (l + 1)) → V x) :
    φ.wedge ((A.extDeriv (l + 1) ψ).interior a) x u =
      φ.wedge (A.lieDeriv (l + 1) a ψ) x u -
        φ.wedge (A.extDeriv l (ψ.interior a)) x u := by
  rw [A.interior_extDeriv_succ, ContMDiffSection.wedge_sub_right]; simp

private theorem extDeriv_wedge_zero_zero (φ ψ : Ω[0]) (x : M) (v : Fin 1 → V x) :
    A.extDeriv 0 (φ.wedge ψ) x v =
      (A.extDeriv 0 φ).wedge ψ x (v ∘ Fin.cast (Nat.succ_add 0 0)) +
        (-1 : ℝ) ^ 0 • (φ.wedge (A.extDeriv 0 ψ)) x v := by
  obtain ⟨a, ha⟩ := ContMDiffSection.exists_apply_eq (I := I) (F := F) ∞ x (v 0)
  simp only [Fin.cast_refl, Function.comp_id]
  rw [ContMDiffSection.apply_eq_interior_tail _ ha, A.interior_extDeriv_zero,
    A.lieDeriv_wedge_apply (k := 0) (l := 0)]
  conv_rhs =>
    lhs; rw [ContMDiffSection.apply_eq_interior_tail (k := 0) _ ha,
      ContMDiffSection.interior_wedge_zero_right, A.interior_extDeriv_zero]
  conv_rhs =>
    rhs; arg 2; rw [ContMDiffSection.apply_eq_interior_tail (k := 0) _ ha,
      ContMDiffSection.interior_wedge_zero_left, A.interior_extDeriv_zero]
  simp

private theorem extDeriv_wedge_succ_zero {k : ℕ} (φ : Ω[k + 1]) (ψ : Ω[0])
    (x : M) (v : Fin (k + 1 + 1) → V x)
    (ih : ∀ (φ' : Ω[k]) (w : Fin (k + 1) → V x), A.extDeriv k (φ'.wedge ψ) x w =
      (A.extDeriv k φ').wedge ψ x (w ∘ Fin.cast (Nat.succ_add k 0)) +
        (-1 : ℝ) ^ k • (φ'.wedge (A.extDeriv 0 ψ)) x w) :
    A.extDeriv (k + 1) (φ.wedge ψ) x v =
      (A.extDeriv (k + 1) φ).wedge ψ x (v ∘ Fin.cast (Nat.succ_add (k + 1) 0)) +
        (-1 : ℝ) ^ (k + 1) • (φ.wedge (A.extDeriv 0 ψ)) x v := by
  obtain ⟨a, ha⟩ := ContMDiffSection.exists_apply_eq (I := I) (F := F) ∞ x (v 0)
  rw [A.extDeriv_succ_apply_eq_sub (m := k) (φ.wedge ψ) ha,
    A.lieDeriv_wedge_apply (k := k + 1) (l := 0), ContMDiffSection.interior_wedge_zero_right,
    ih (φ.interior a) (Fin.tail v)]
  simp only [Fin.cast_refl, Function.comp_id]
  rw [ContMDiffSection.apply_eq_interior_tail (k := k + 1) ((A.extDeriv (k + 1) φ).wedge ψ) ha,
    ContMDiffSection.interior_wedge_zero_right, A.interior_extDeriv_succ_wedge_left,
    ContMDiffSection.apply_eq_interior_tail (k := k + 1) (φ.wedge (A.extDeriv 0 ψ)) ha,
    ContMDiffSection.interior_wedge_succ_apply, Fin.cast_refl, Function.comp_id,
    A.interior_extDeriv_zero]
  rcases neg_one_pow_eq_or ℝ k with hk | hk <;>
    simp only [smul_eq_mul, pow_succ (-1 : ℝ), hk] <;> ring

private theorem extDeriv_wedge_zero_succ {l : ℕ} (φ : Ω[0]) (ψ : Ω[l + 1])
    (x : M) (v : Fin (0 + (l + 1) + 1) → V x)
    (ih : ∀ (ψ' : Ω[l]) (w : Fin (0 + l + 1) → V x), A.extDeriv (0 + l) (φ.wedge ψ') x w =
      (A.extDeriv 0 φ).wedge ψ' x (w ∘ Fin.cast (Nat.succ_add 0 l)) +
        (-1 : ℝ) ^ 0 • (φ.wedge (A.extDeriv l ψ')) x w) :
    A.extDeriv (0 + (l + 1)) (φ.wedge ψ) x v =
      (A.extDeriv 0 φ).wedge ψ x (v ∘ Fin.cast (Nat.succ_add 0 (l + 1))) +
        (-1 : ℝ) ^ 0 • (φ.wedge (A.extDeriv (l + 1) ψ)) x v := by
  obtain ⟨a, ha⟩ := ContMDiffSection.exists_apply_eq (I := I) (F := F) ∞ x (v 0)
  set v₀ : Fin ((0 + 1) + (l + 1)) → V x := v ∘ Fin.cast (Nat.succ_add 0 (l + 1))
  have ha₀ : a x = v₀ 0 := ha
  have htail₁ : Fin.tail v₀ ∘ Fin.cast (Nat.add_right_comm 0 1 l).symm = Fin.tail v := by
    ext i; simp [v₀, Fin.tail]
  have htail₂ : Fin.tail v₀ = Fin.tail v ∘ Fin.cast (Nat.succ_add 0 l) := by
    ext i; simp [v₀, Fin.tail]
  rw [A.extDeriv_wedge_succ_right_apply φ ψ ha, ContMDiffSection.interior_wedge_zero_left,
    ih (ψ.interior a) (Fin.tail v),
    ContMDiffSection.apply_eq_interior_tail (k := 0 + 1 + l) ((A.extDeriv 0 φ).wedge ψ) ha₀,
    ContMDiffSection.interior_wedge_succ_apply, htail₁, htail₂, A.interior_extDeriv_zero,
    ContMDiffSection.apply_eq_interior_tail (k := 0 + (l + 1))
      (φ.wedge (A.extDeriv (l + 1) ψ)) ha,
    ContMDiffSection.interior_wedge_zero_left, A.wedge_interior_extDeriv_succ_right]
  simp only [pow_zero, smul_eq_mul]; ring

private theorem extDeriv_interior_wedge_succ {k l : ℕ} (φ : Ω[k + 1]) (ψ : Ω[l + 1])
    (a : Cₛ^∞⟮I; F, V⟯) (x : M) (u : Fin (k + 1 + l + 1) → V x) :
    A.extDeriv (k + 1 + l) ((φ.wedge ψ).interior a) x u =
      A.extDeriv (k + (l + 1)) ((φ.interior a).wedge ψ) x
          (u ∘ Fin.cast (congrArg (· + 1) (Nat.add_right_comm k 1 l).symm)) +
        (-1 : ℝ) ^ (k + 1) • A.extDeriv (k + 1 + l) (φ.wedge (ψ.interior a)) x u := by
  rw [ContMDiffSection.interior_wedge_succ, map_add, map_smul, A.extDeriv_cast,
    ContMDiffSection.add_cast_smul_apply]
  -- `k + 1 + l` and `k + (l + 1)` are definitionally equal, and the `Fin.cast` proof on `u`
  -- matches the stated one up to proof irrelevance.
  rfl

private theorem extDeriv_wedge_succ_succ {k l : ℕ} (φ : Ω[k + 1]) (ψ : Ω[l + 1])
    (x : M) (v : Fin ((k + 1) + (l + 1) + 1) → V x)
    (ih₁ : ∀ (φ' : Ω[k]) (w : Fin (k + (l + 1) + 1) → V x),
      A.extDeriv (k + (l + 1)) (φ'.wedge ψ) x w =
        (A.extDeriv k φ').wedge ψ x (w ∘ Fin.cast (Nat.succ_add k (l + 1))) +
          (-1 : ℝ) ^ k • (φ'.wedge (A.extDeriv (l + 1) ψ)) x w)
    (ih₂ : ∀ (ψ' : Ω[l]) (w : Fin ((k + 1) + l + 1) → V x),
      A.extDeriv ((k + 1) + l) (φ.wedge ψ') x w =
        (A.extDeriv (k + 1) φ).wedge ψ' x (w ∘ Fin.cast (Nat.succ_add (k + 1) l)) +
          (-1 : ℝ) ^ (k + 1) • (φ.wedge (A.extDeriv l ψ')) x w) :
    A.extDeriv ((k + 1) + (l + 1)) (φ.wedge ψ) x v =
      (A.extDeriv (k + 1) φ).wedge ψ x (v ∘ Fin.cast (Nat.succ_add (k + 1) (l + 1))) +
        (-1 : ℝ) ^ (k + 1) • (φ.wedge (A.extDeriv (l + 1) ψ)) x v := by
  obtain ⟨a, ha⟩ := ContMDiffSection.exists_apply_eq (I := I) (F := F) ∞ x (v 0)
  set v₀ : Fin ((k + 1 + 1) + (l + 1)) → V x := v ∘ Fin.cast (Nat.succ_add (k + 1) (l + 1))
  let w₂ : Fin (k + (l + 1) + 1) → V x :=
    Fin.tail v ∘ Fin.cast (congrArg (· + 1) (Nat.add_right_comm k 1 l).symm)
  let w₃ : Fin ((k + 1 + 1) + l) → V x := Fin.tail v ∘ Fin.cast (Nat.succ_add (k + 1) l)
  have ht₁ : w₂ ∘ Fin.cast (Nat.succ_add k (l + 1)) = Fin.tail v := by ext i; simp [w₂, Fin.tail]
  have ht₂ : Fin.tail v₀ ∘ Fin.cast (Nat.add_right_comm (k + 1) 1 l).symm = Fin.tail v := by
    ext i; simp [v₀, Fin.tail]
  have ht₃ : Fin.tail v₀ = w₃ := by ext i; simp [v₀, w₃, Fin.tail]
  rw [A.extDeriv_wedge_succ_right_apply φ ψ ha, A.extDeriv_interior_wedge_succ,
    ih₁ (φ.interior a) w₂, ht₁, ih₂ (ψ.interior a) (Fin.tail v),
    ContMDiffSection.apply_eq_interior_tail (k := k + 1 + 1 + l)
      ((A.extDeriv (k + 1) φ).wedge ψ) ha,
    ContMDiffSection.interior_wedge_succ_apply, ht₂, ht₃,
    A.interior_extDeriv_succ_wedge_left,
    ContMDiffSection.apply_eq_interior_tail (k := (k + 1) + (l + 1))
      (φ.wedge (A.extDeriv (l + 1) ψ)) ha,
    ContMDiffSection.interior_wedge_succ_apply, A.wedge_interior_extDeriv_succ_right]
  rcases neg_one_pow_eq_or ℝ k with hk | hk <;>
    simp only [smul_eq_mul, pow_succ (-1 : ℝ), hk] <;> ring

/-- Pointwise **graded derivation law** for the algebroid exterior derivative on the fibrewise
wedge product: `d_A (φ ∧ ψ) = d_A φ ∧ ψ + (-1)^k φ ∧ d_A ψ` up to
`Fin.cast (Nat.succ_add k l)`. -/
theorem extDeriv_wedge_apply {k l : ℕ} (φ : Ω[k]) (ψ : Ω[l]) (x : M)
    (v : Fin (k + l + 1) → V x) :
    A.extDeriv (k + l) (φ.wedge ψ) x v =
      (A.extDeriv k φ).wedge ψ x (v ∘ Fin.cast (Nat.succ_add k l)) +
        (-1 : ℝ) ^ k • (φ.wedge (A.extDeriv l ψ)) x v := by
  -- Induct on `k + l`, reducing via Cartan's magic formula `ι_a d_A + d_A ι_a = L_a`.
  suffices h : ∀ n : ℕ, ∀ {k l : ℕ}, k + l = n →
      ∀ (φ : Ω[k]) (ψ : Ω[l]) (v : Fin (k + l + 1) → V x),
        A.extDeriv (k + l) (φ.wedge ψ) x v =
          (A.extDeriv k φ).wedge ψ x (v ∘ Fin.cast (Nat.succ_add k l)) +
            (-1 : ℝ) ^ k • (φ.wedge (A.extDeriv l ψ)) x v from h (k + l) rfl φ ψ v
  intro n; induction n using Nat.strongRecOn with
  | ind n ih =>
    rintro k l rfl φ ψ v
    rcases k with _ | k <;> rcases l with _ | l
    · exact A.extDeriv_wedge_zero_zero φ ψ x v
    · exact A.extDeriv_wedge_zero_succ φ ψ x v fun ψ' w ↦ ih (0 + l) (by omega) rfl φ ψ' w
    · exact A.extDeriv_wedge_succ_zero φ ψ x v fun φ' w ↦ ih (k + 0) (by omega) rfl φ' ψ w
    · exact A.extDeriv_wedge_succ_succ φ ψ x v
        (fun φ' w ↦ ih (k + (l + 1)) (by omega) rfl φ' ψ w)
        (fun ψ' w ↦ ih ((k + 1) + l) (by omega) rfl φ ψ' w)

/-- **Graded derivation law** for the algebroid exterior derivative on the fibrewise wedge product:
`d_A (φ ∧ ψ) = LinearEquiv.cast ... (Nat.succ_add k l) (d_A φ ∧ ψ) + (-1)^k • (φ ∧ d_A ψ)`. -/
theorem extDeriv_wedge {k l : ℕ} (φ : Ω[k]) (ψ : Ω[l]) :
    A.extDeriv (k + l) (φ.wedge ψ) =
      LinearEquiv.cast (R := C^∞⟮I, M; ℝ⟯) (M := fun q : ℕ ↦ Ω[q]) (Nat.succ_add k l)
          ((A.extDeriv k φ).wedge ψ) +
        (-1 : ℝ) ^ k • φ.wedge (A.extDeriv l ψ) := by
  ext x v
  rw [ContMDiffSection.add_cast_smul_apply]
  exact A.extDeriv_wedge_apply φ ψ x v

/-- Leibniz rule for `A.extDeriv` under scalar multiplication by a smooth function `f`:
`d_A (f • φ) = f • d_A φ + LinearEquiv.cast ... (Nat.add_comm 1 k) (d_A f ∧ φ)`. -/
theorem extDeriv_smul {k : ℕ} (f : C^∞⟮I, M; ℝ⟯) (φ : Ω[k]) :
    A.extDeriv k (f • φ) =
      f • A.extDeriv k φ +
        LinearEquiv.cast (R := C^∞⟮I, M; ℝ⟯) (M := fun q : ℕ ↦ Ω[q]) (Nat.add_comm 1 k)
          ((A.extDeriv 0 (ContMDiffSection.constOfIsEmptyEquiv I F ∞ V (Fin 0) f)).wedge φ) := by
  let f₀ := ContMDiffSection.constOfIsEmptyEquiv I F ∞ V (Fin 0) f
  have hfφ : φ.wedge f₀ = f • φ := by simp [f₀]
  have hdfφ : (A.extDeriv k φ).wedge f₀ = f • A.extDeriv k φ := by simp [f₀]
  have h := A.extDeriv_wedge (k := k) (l := 0) φ f₀
  dsimp only [Nat.add_zero] at h
  rw [hfφ, LinearEquiv.cast_apply, cast_eq, hdfφ,
    ContMDiffSection.wedge_comm φ (A.extDeriv 0 f₀), Nat.mul_one, smul_smul, ← pow_add,
    ← two_mul, (even_two_mul k).neg_one_pow, one_smul] at h
  exact h

/-- Pointwise Leibniz rule for `A.extDeriv` under scalar multiplication by a smooth function `f`:
`d_A (f • φ) = f • d_A φ + d_A f ∧ φ` up to `Fin.cast (Nat.add_comm 1 k)`. -/
theorem extDeriv_smul_apply {k : ℕ} (f : C^∞⟮I, M; ℝ⟯) (φ : Ω[k]) (x : M)
    (v : Fin (k + 1) → V x) :
    A.extDeriv k (f • φ) x v =
      f x • A.extDeriv k φ x v +
        (A.extDeriv 0 (ContMDiffSection.constOfIsEmptyEquiv I F ∞ V (Fin 0) f)).wedge φ x
          (v ∘ Fin.cast (Nat.add_comm 1 k)) := by
  simpa [-LinearEquiv.cast_apply, ContMDiffSection.cast_apply] using
    congr($(A.extDeriv_smul f φ) x v)

end General

/-- Converting the smooth real wedge of two forms to a section gives the fibrewise wedge of their
converted sections. -/
@[simp]
theorem _root_.TauCeti.SmoothForm.wedge_toContMDiffSection
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
    [IsManifold I 1 M] {k l : ℕ}
    (φ : TauCeti.SmoothForm I M ℝ k) (ψ : TauCeti.SmoothForm I M ℝ l) :
    (TauCeti.SmoothForm.wedge φ ψ).toContMDiffSection =
      φ.toContMDiffSection.wedge ψ.toContMDiffSection := by
  ext x v
  simp only [TauCeti.SmoothForm.toContMDiffSection_apply, ContMDiffSection.wedge_apply_sum]
  exact TauCeti.SmoothForm.wedge_apply φ ψ x v

/-! ### Comparison with the de Rham exterior derivative on the tangent Lie algebroid -/

section Tangent

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

/-- On the tangent Lie algebroid `TauCeti.LieAlgebroid.tangent I M`, the algebroid exterior
derivative `extDeriv` coincides with the manifold exterior derivative `TauCeti.mextDerivₗ` via
`SmoothForm.toContMDiffSection`. -/
theorem tangent_extDeriv_toContMDiffSection (k : ℕ) (φ : SmoothForm I M ℝ k) :
    (tangent I M).extDeriv k (SmoothForm.toContMDiffSection φ) =
      SmoothForm.toContMDiffSection (mextDerivₗ I k φ) := by
  refine ContMDiffSection.eq_of_evalAlternating_eq <| AlternatingMap.ext fun s ↦ ?_
  ext x
  cases k with
  | zero =>
    have hs : (fun i : Fin 1 ↦ s i x) = ![s 0 x] := funext fun i ↦ by fin_cases i; rfl
    have hφ0 : ⇑((SmoothForm.toContMDiffSection φ).evalAlternating ![]) = fun y ↦ φ.val y 0 := by
      ext y; rw [ContMDiffSection.evalAlternating_apply, SmoothForm.toContMDiffSection_apply]
      exact congrArg (φ.val y) (Subsingleton.elim _ _)
    rw [evalAlternating_extDeriv_zero, anchorDeriv_apply, tangent_anchor_apply, hφ0,
      ContMDiffSection.evalAlternating_apply, SmoothForm.toContMDiffSection_apply, hs,
      mextDerivₗ_zero_apply]
  | succ n =>
    have hV (i : Fin (n + 2)) :
        MDifferentiableAt I I.tangent (fun y ↦ (s i y : TangentBundle I M)) x :=
      (s i).contMDiff.mdifferentiableAt (by simp)
    have heval (i : Fin (n + 2)) :
        ⇑((SmoothForm.toContMDiffSection φ).evalAlternating (i.removeNth s)) =
          fun y ↦ φ.val y (i.removeNth (fun r ↦ s r y)) := by
      ext y; rw [ContMDiffSection.evalAlternating_apply, SmoothForm.toContMDiffSection_apply]
      congr 1
    have hcons (i j : Fin (n + 1)) :
        (fun r ↦
          Matrix.vecCons ((tangent I M).bracket (s i.castSucc) (s j.succ))
            (j.removeNth (i.castSucc.removeNth s)) r x) =
          Matrix.vecCons (mlieBracket I (s i.castSucc) (s j.succ) x)
            (j.removeNth (i.castSucc.removeNth (fun r ↦ s r x))) := by
      funext r; exact Fin.cases (by simp) (fun _ ↦ by simp [Fin.removeNth]) r
    rw [← ContMDiffMap.evalAlgHom_apply ℝ x, evalAlternating_extDeriv_succ,
      ContMDiffSection.evalAlternating_apply, SmoothForm.toContMDiffSection_apply,
      mextDerivₗ_apply, SmoothForm.mextDeriv_apply_vectorField hV]
    simp only [map_add, map_sum, map_zsmul, ContMDiffMap.evalAlgHom_apply]
    simp only [anchorDeriv_apply, tangent_anchor_apply, heval,
      ContMDiffSection.evalAlternating_apply, SmoothForm.toContMDiffSection_apply, hcons,
      zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, pow_succ (-1 : ℝ), mul_neg_one,
      neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg]

variable (I M) in
/-- The Chevalley–Eilenberg cochain complex of the tangent Lie algebroid `tangent I M` is
canonically isomorphic to the de Rham complex `deRhamComplex I M`, via
`SmoothForm.ofContMDiffSection` and `SmoothForm.toContMDiffSection`. -/
def tangentCochainComplexIso : (tangent I M).cochainComplex ≅ deRhamComplex I M :=
  HomologicalComplex.Hom.isoOfComponents
    (fun k ↦ (tangent I M).cochainComplexXIso k ≪≫
      (SmoothForm.toContMDiffSectionEquiv I M ℝ k).symm.toModuleIso ≪≫
      (deRhamComplexXIso I k).symm) <| by
    rintro k _ rfl
    have hcomm :
        (SmoothForm.toContMDiffSectionEquiv I M ℝ k).symm.toModuleIso.hom ≫
            ModuleCat.ofHom (mextDerivₗ I (F := ℝ) k) =
          ModuleCat.ofHom ((tangent I M).extDeriv k) ≫
            (SmoothForm.toContMDiffSectionEquiv I M ℝ (k + 1)).symm.toModuleIso.hom := by
      ext s : 2
      apply SmoothForm.toContMDiffSection_injective
      simp only [ModuleCat.hom_comp, LinearEquiv.toModuleIso_hom, LinearMap.comp_apply,
        ModuleCat.hom_ofHom, LinearEquiv.coe_coe, SmoothForm.toContMDiffSectionEquiv_symm_apply]
      rw [← tangent_extDeriv_toContMDiffSection, SmoothForm.toContMDiffSection_ofContMDiffSection,
        SmoothForm.toContMDiffSection_ofContMDiffSection]
    rw [(Iso.eq_comp_inv _).mpr (deRhamComplex_d I (M := M) k),
      (Iso.eq_comp_inv _).mpr ((tangent I M).cochainComplex_d_succ k)]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hcomm]

/-- On degree-`k` components read through `cochainComplexXIso` and `deRhamComplexXIso`, the
forward isomorphism `(tangentCochainComplexIso I M).hom.f k` is `SmoothForm.ofContMDiffSection`. -/
@[simp]
theorem tangentCochainComplexIso_hom_f_apply (k : ℕ) (x : (tangent I M).cochainComplex.X k) :
    (deRhamComplexXIso I k).hom ((tangentCochainComplexIso I M).hom.f k x) =
      SmoothForm.ofContMDiffSection (((tangent I M).cochainComplexXIso k).hom x) := by
  simp [tangentCochainComplexIso]

/-- On degree-`k` components read through `deRhamComplexXIso` and `cochainComplexXIso`, the
inverse isomorphism `(tangentCochainComplexIso I M).inv.f k` is `SmoothForm.toContMDiffSection`. -/
@[simp]
theorem tangentCochainComplexIso_inv_f_apply (k : ℕ) (x : (deRhamComplex I M).X k) :
    ((tangent I M).cochainComplexXIso k).hom ((tangentCochainComplexIso I M).inv.f k x) =
      SmoothForm.toContMDiffSection ((deRhamComplexXIso I k).hom x) := by
  simp [tangentCochainComplexIso]

/-- Evaluating `(tangentCochainComplexIso I M).hom.f k` on a section inserted via
`cochainComplexXIso` yields `SmoothForm.ofContMDiffSection` inserted via `deRhamComplexXIso`. -/
@[simp]
theorem tangentCochainComplexIso_hom_f_inv_apply (k : ℕ)
    (s : Cₛ^∞⟮I; E [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ⟯) :
    (tangentCochainComplexIso I M).hom.f k (((tangent I M).cochainComplexXIso k).inv s) =
      (deRhamComplexXIso I k).inv (SmoothForm.ofContMDiffSection s) := by
  simp [tangentCochainComplexIso]

/-- Evaluating `(tangentCochainComplexIso I M).inv.f k` on a smooth form inserted via
`deRhamComplexXIso` yields `SmoothForm.toContMDiffSection` inserted via `cochainComplexXIso`. -/
@[simp]
theorem tangentCochainComplexIso_inv_f_inv_apply (k : ℕ) (φ : SmoothForm I M ℝ k) :
    (tangentCochainComplexIso I M).inv.f k ((deRhamComplexXIso I k).inv φ) =
      ((tangent I M).cochainComplexXIso k).inv (SmoothForm.toContMDiffSection φ) := by
  simp [tangentCochainComplexIso]

variable (I M) in
/-- The `k`-th Chevalley–Eilenberg cohomology of the tangent Lie algebroid `tangent I M` is
canonically isomorphic to the `k`-th de Rham cohomology of `M`. -/
def tangentCohomologyIso (k : ℕ) :
    (tangent I M).cohomology k ≅ (deRhamComplex I M).homology k :=
  (HomologicalComplex.homologyFunctor _ _ k).mapIso (tangentCochainComplexIso I M)

end Tangent

end TauCeti.LieAlgebroid
