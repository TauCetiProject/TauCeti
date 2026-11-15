/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Algebra.VanishingIdeal.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Module
import Mathlib.Geometry.Manifold.BumpFunction
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import TauCeti.Geometry.Manifold.VectorBundle.Tensoriality

/-!
# The fibre of a vector bundle as sections modulo the vanishing ideal

Let `V` be a smooth real vector bundle of finite rank over a finite-dimensional Hausdorff smooth
manifold `M`, and let `I_x` be the ideal of smooth real functions vanishing at `x`. The smooth
sections `Γ(V)` form a module over `C^∞(M)`, and its submodule `I_x Γ(V)` consists of the finite
sums `∑ fᵢ sᵢ` with `fᵢ(x) = 0`. A smooth section lies in `I_x Γ(V)` exactly when it vanishes at
`x`, so evaluation at `x` identifies the quotient `Γ(V) / I_x Γ(V)` with the fibre `V_x`.

Together with `TauCeti.smoothCotangentEquiv`, which identifies `I_x / I_x²` with the cotangent
space `T_x*M` at interior points `x`, this turns the algebraic description of differential
operators between modules of sections into fibrewise statements: a `C^∞(M)`-linear construction
on sections that descends to the quotients by `I_x Γ(V)` becomes a map between fibres at `x`.

Finite rank enters through local frames: near `x` a section is a finite combination of frame
sections, which is what makes `I_x Γ(V)`, a submodule of *finite* sums, large enough.

## Main results

* `TauCeti.mem_smoothVanishingIdeal_smul_top_iff`: a smooth section lies in `I_x Γ(V)` if and
  only if it vanishes at `x`.
* `ContMDiffSection.ker_evalLinearMap`: the kernel of evaluation at `x` is `I_x Γ(V)`.
* `TauCeti.smoothSectionFiberEquiv`: the real-linear equivalence `Γ(V) / I_x Γ(V) ≃ V_x` sending
  the class of `s` to `s x`, and `TauCeti.smoothSectionFiberEquiv_smul`, its compatibility with
  multiplication by smooth functions through evaluation at `x`.
* `TauCeti.smoothSectionLinearMap_apply_eq_of_apply_eq`: a map of sections that is linear over the
  smooth functions is tensorial, its value at `x` only depends on the value of the section at `x`.
* `TauCeti.smoothSectionFiberMap`: the fibre map `V_x → W_x` at `x` of such a map of sections.

## Implementation notes

A section vanishing near `x` is `(1 - χ) s` for a bump function `χ` equal to one near `x`, so it
lies in `I_x Γ(V)`. The class of a section modulo `I_x Γ(V)` is an additive operation, and
`f s - f(x) s = (f - f(x)) s` shows it is linear over smooth functions through evaluation at
`x`. The tensoriality criterion `TauCeti.Manifold.eq_of_contMDiff_tensorial`, proved by a cut-off
local frame expansion, then shows that this class depends only on the value at `x`.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural operations in differential geometry*, Springer,
  1993, §§1.3–1.6 and §12.
-/

public section

noncomputable section

open Bundle Filter
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- A section in `I_x Γ(V)` vanishes at `x`. -/
theorem apply_eq_zero_of_mem_smoothVanishingIdeal_smul_top {x : M} {s : Cₛ^∞⟮I; F, V⟯}
    (hs : s ∈ smoothVanishingIdeal I x • (⊤ : Submodule C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯)) :
    s x = 0 := by
  refine Submodule.smul_induction_on (p := fun s : Cₛ^∞⟮I; F, V⟯ ↦ s x = 0) hs ?_ ?_
  · intro f hf t _
    simp [mem_smoothVanishingIdeal_iff.mp hf]
  · intro s t hs ht
    simp [hs, ht]

variable [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M]

/-- A smooth section vanishing on a neighbourhood of `x` lies in `I_x ^ m Γ(V)` for every `m`. -/
theorem mem_smoothVanishingIdeal_pow_smul_top_of_eventuallyEq_zero {x : M} {s : Cₛ^∞⟮I; F, V⟯}
    (hs : ∀ᶠ y in 𝓝 x, s y = 0) (m : ℕ) :
    s ∈ smoothVanishingIdeal I x ^ m • (⊤ : Submodule C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯) := by
  obtain ⟨ρ, -, hρ⟩ := (SmoothBumpFunction.nhds_basis_support (I := I) hs).mem_iff.mp hs
  let χ : C^∞⟮I, M; ℝ⟯ := ⟨ρ, ρ.contMDiff⟩
  have hχ : ⇑χ = ρ := ContMDiffMap.coeFn_mk _ _
  have hfac : s = (1 - χ) ^ m • s := by
    ext y
    by_cases hy : ρ y = 0
    · simp [hχ, hy]
    · simp [(hρ (Function.mem_support.mpr hy)).out]
  rw [hfac]
  exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (by simp [hχ]) m) Submodule.mem_top

/-- A smooth section vanishing on a neighbourhood of `x` lies in `I_x Γ(V)`. -/
theorem mem_smoothVanishingIdeal_smul_top_of_eventuallyEq_zero {x : M} {s : Cₛ^∞⟮I; F, V⟯}
    (hs : ∀ᶠ y in 𝓝 x, s y = 0) :
    s ∈ smoothVanishingIdeal I x • (⊤ : Submodule C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯) := by
  simpa using mem_smoothVanishingIdeal_pow_smul_top_of_eventuallyEq_zero hs 1

variable [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I]

/-- **A section vanishing at a point is a finite sum of products with functions vanishing
there.** A smooth section of a finite-rank bundle vanishing at `x` lies in `I_x Γ(V)`. -/
theorem mem_smoothVanishingIdeal_smul_top_of_apply_eq_zero {x : M} {s : Cₛ^∞⟮I; F, V⟯}
    (hs : s x = 0) :
    s ∈ smoothVanishingIdeal I x • (⊤ : Submodule C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯) := by
  classical
  let N := smoothVanishingIdeal I x • (⊤ : Submodule C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯)
  -- The class modulo `I_x Γ(V)` of a smooth section, extended by zero to all sections.
  let Φ : (Π y : M, V y) → Cₛ^∞⟮I; F, V⟯ ⧸ N := fun u ↦
    if hu : CMDiff ∞ (T% u) then Submodule.Quotient.mk ⟨u, hu⟩ else 0
  have hΦ {u : Π y : M, V y} (hu : CMDiff ∞ (T% u)) : Φ u = Submodule.Quotient.mk ⟨u, hu⟩ :=
    dite_eq_left hu
  -- `Φ` is tensorial, so it only depends on the value at `x`.
  have h := Manifold.eq_of_contMDiff_tensorial (I := I) Φ x
    (fun hu hu' ↦ by
      rw [hΦ (hu.add_section hu'), hΦ hu, hΦ hu', ← Submodule.Quotient.mk_add]
      exact congrArg _ (ContMDiffSection.ext fun y ↦ by simp))
    (fun {f u} hf hu ↦ by
      rw [hΦ (hf.smul_section hu), hΦ hu, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
      let g : C^∞⟮I, M; ℝ⟯ := ⟨fun y ↦ f y - f x, hf.sub contMDiff_const⟩
      have hg_apply (y : M) : g y = f y - f x := rfl
      have hg : (⟨f • u, hf.smul_section hu⟩ : Cₛ^∞⟮I; F, V⟯) - f x • ⟨u, hu⟩ = g • ⟨u, hu⟩ := by
        ext y
        simp [hg_apply, sub_smul]
      rw [hg]
      exact Submodule.smul_mem_smul (by rw [mem_smoothVanishingIdeal_iff, hg_apply, sub_self])
        Submodule.mem_top)
    s.contMDiff (contMDiff_zeroSection ℝ V) (by simpa using hs)
  rw [hΦ s.contMDiff, hΦ (contMDiff_zeroSection ℝ V)] at h
  exact (Submodule.Quotient.mk_eq_zero N).mp (h.trans ((Submodule.Quotient.mk_eq_zero N).mpr
    (Submodule.zero_mem N)))

/-- A smooth section of a finite-rank bundle lies in `I_x Γ(V)`, the submodule of finite sums of
products with smooth functions vanishing at `x`, if and only if it vanishes at `x`. -/
@[simp]
theorem mem_smoothVanishingIdeal_smul_top_iff {x : M} {s : Cₛ^∞⟮I; F, V⟯} :
    s ∈ smoothVanishingIdeal I x • (⊤ : Submodule C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯) ↔ s x = 0 :=
  ⟨apply_eq_zero_of_mem_smoothVanishingIdeal_smul_top,
    mem_smoothVanishingIdeal_smul_top_of_apply_eq_zero⟩

end TauCeti

namespace ContMDiffSection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- The kernel of evaluation at `x` on smooth sections of a finite-rank bundle is `I_x Γ(V)`. -/
theorem ker_evalLinearMap [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I] (x : M) :
    LinearMap.ker (evalLinearMap I F ∞ V x) =
      (TauCeti.smoothVanishingIdeal I x •
        (⊤ : Submodule C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯)).restrictScalars ℝ := by
  ext s
  simp [TauCeti.mem_smoothVanishingIdeal_smul_top_iff]

end ContMDiffSection

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]

variable (I F V) in
/-- **The fibre of a vector bundle is the module of sections modulo the vanishing ideal.** For a
smooth real vector bundle `V` of finite rank over a finite-dimensional Hausdorff manifold,
evaluation at `x` induces a real-linear equivalence `Γ(V) / I_x Γ(V) ≃ V_x`. -/
def smoothSectionFiberEquiv (x : M) :
    (Cₛ^∞⟮I; F, V⟯ ⧸ smoothVanishingIdeal I x • (⊤ : Submodule C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯)) ≃ₗ[ℝ]
      V x :=
  (Submodule.Quotient.restrictScalarsEquiv ℝ _).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (ContMDiffSection.ker_evalLinearMap x).symm ≪≫ₗ
    (ContMDiffSection.evalLinearMap I F ∞ V x).quotKerEquivOfSurjective
      (ContMDiffSection.evalLinearMap_surjective ∞ x)

/-- The equivalence `Γ(V) / I_x Γ(V) ≃ V_x` sends the class of a section to its value at `x`. -/
@[simp]
theorem smoothSectionFiberEquiv_mk (x : M) (s : Cₛ^∞⟮I; F, V⟯) :
    smoothSectionFiberEquiv I F V x (Submodule.Quotient.mk s) = s x := by
  simp [smoothSectionFiberEquiv]

/-- The inverse of `Γ(V) / I_x Γ(V) ≃ V_x` sends the value of a section at `x` to its class. -/
@[simp]
theorem smoothSectionFiberEquiv_symm_apply (x : M) (s : Cₛ^∞⟮I; F, V⟯) :
    (smoothSectionFiberEquiv I F V x).symm (s x) = Submodule.Quotient.mk s := by
  rw [LinearEquiv.symm_apply_eq, smoothSectionFiberEquiv_mk]

/-- The equivalence `Γ(V) / I_x Γ(V) ≃ V_x` turns multiplication by a smooth function into
multiplication by its value at `x`. -/
@[simp]
theorem smoothSectionFiberEquiv_smul (x : M) (f : C^∞⟮I, M; ℝ⟯)
    (q : Cₛ^∞⟮I; F, V⟯ ⧸ smoothVanishingIdeal I x • (⊤ : Submodule C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯)) :
    smoothSectionFiberEquiv I F V x (f • q) = f x • smoothSectionFiberEquiv I F V x q := by
  induction q using Submodule.Quotient.induction_on with
  | H s => rw [← Submodule.Quotient.mk_smul, smoothSectionFiberEquiv_mk,
      smoothSectionFiberEquiv_mk, ContMDiffSection.smul_apply]

/-! ### Linear maps over smooth functions are tensorial -/

section Tensorial

variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {W : M → Type*} [TopologicalSpace (TotalSpace F' W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [FiberBundle F' W] [VectorBundle ℝ F' W]

/-- A map of sections that is linear over the smooth functions sends a section vanishing at `x`
to a section vanishing at `x`. -/
theorem smoothSectionLinearMap_apply_eq_zero_of_apply_eq_zero
    (L : Cₛ^∞⟮I; F, V⟯ →ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; F', W⟯) {x : M} {s : Cₛ^∞⟮I; F, V⟯}
    (hs : s x = 0) : L s x = 0 := by
  refine apply_eq_zero_of_mem_smoothVanishingIdeal_smul_top ?_
  have h := Submodule.mem_map_of_mem (f := L)
    (mem_smoothVanishingIdeal_smul_top_of_apply_eq_zero hs)
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h

/-- **Tensoriality.** The value at `x` of the image of a section under a map of sections that is
linear over the smooth functions only depends on the value of the section at `x`. -/
theorem smoothSectionLinearMap_apply_eq_of_apply_eq
    (L : Cₛ^∞⟮I; F, V⟯ →ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; F', W⟯) {x : M} {s t : Cₛ^∞⟮I; F, V⟯}
    (h : s x = t x) : L s x = L t x := by
  have hst := smoothSectionLinearMap_apply_eq_zero_of_apply_eq_zero L (x := x) (s := s - t)
    (by simp [h])
  rwa [map_sub, ContMDiffSection.coe_sub, Pi.sub_apply, sub_eq_zero] at hst

omit [FiniteDimensional ℝ F] in
variable (I F V) in
private theorem exists_evalLinearMap_comp_eq_id (x : M) :
    ∃ g : V x →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯, ContMDiffSection.evalLinearMap I F ∞ V x ∘ₗ g = LinearMap.id :=
  LinearMap.exists_rightInverse_of_surjective _ <|
    LinearMap.range_eq_top.2 (ContMDiffSection.evalLinearMap_surjective ∞ x)

omit [FiniteDimensional ℝ F] in
variable (I F V F' W) in
/-- The fibre map at `x` of a map of sections that is linear over the smooth functions: the
real-linear map `V_x → W_x` sending `s x` to `L s x`
(`TauCeti.smoothSectionFiberMap_apply_apply`), well defined by tensoriality when `V` has finite
rank. -/
def smoothSectionFiberMap (x : M) :
    (Cₛ^∞⟮I; F, V⟯ →ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; F', W⟯) →ₗ[ℝ] (V x →ₗ[ℝ] W x) where
  toFun L := ContMDiffSection.evalLinearMap I F' ∞ W x ∘ₗ L.restrictScalars ℝ ∘ₗ
    (exists_evalLinearMap_comp_eq_id I F V x).choose
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-- The fibre map at `x` of a `C^∞(M)`-linear map of sections `L` sends `s x` to `L s x`. -/
@[simp]
theorem smoothSectionFiberMap_apply_apply (L : Cₛ^∞⟮I; F, V⟯ →ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; F', W⟯)
    {x : M} (s : Cₛ^∞⟮I; F, V⟯) : smoothSectionFiberMap I F V F' W x L (s x) = L s x := by
  have h := LinearMap.congr_fun (exists_evalLinearMap_comp_eq_id I F V x).choose_spec (s x)
  rw [LinearMap.comp_apply, ContMDiffSection.evalLinearMap_apply, LinearMap.id_apply] at h
  simp only [smoothSectionFiberMap, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, ContMDiffSection.evalLinearMap_apply]
  exact smoothSectionLinearMap_apply_eq_of_apply_eq L h

end Tensorial

end TauCeti
