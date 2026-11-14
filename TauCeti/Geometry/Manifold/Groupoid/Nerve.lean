/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Basic
public import TauCeti.Geometry.Manifold.FiberProduct.Identity
public import TauCeti.Geometry.Manifold.Groupoid.Basic
public import TauCeti.Geometry.Manifold.PullbackGroupoid
public import TauCeti.Geometry.Manifold.SmoothEmbedding.LeftInverse
public import TauCeti.Topology.CategoryTheory.ComposableArrows

/-!
# The smooth nerve of a Lie groupoid

For a Lie groupoid `C` with object model `I` (dimension `m`) and arrow model `J` (dimension `d`),
the `k`-th level `ComposableArrows C k` of its topological nerve carries a canonical `C^∞` manifold
structure compatible with `ComposableArrows.instTopologicalSpace`:

* in degree `0`, `ComposableArrows.zeroHomeomorph` identifies `ComposableArrows C 0` with `C`
  (`IsLieGroupoid.zeroDiffeomorph`);
* in degree `k + 1`, `ComposableArrows.precompHomeomorph` identifies `ComposableArrows C (k + 1)`
  with `{p : Quiver.Total C × ComposableArrows C k // p.1.right = p.2.left}` over the submersion
  `Quiver.Total.right` (`IsLieGroupoid.precompDiffeomorph`).

In particular, a map into `ComposableArrows C k` is smooth if and only if each total arrow
`F.totalArrow i j hij` depends smoothly on the parameter (`IsLieGroupoid.contMDiff_nerve_iff`). As
immediate consequences:

* every simplicial operator `(nerve C).map f`, and hence every face map `(nerve C).δ i` and every
  degeneracy map `(nerve C).σ i`, is smooth (`IsLieGroupoid.contMDiff_nerve_map`,
  `IsLieGroupoid.contMDiff_nerve_δ`, `IsLieGroupoid.contMDiff_nerve_σ`);
* every degeneracy map `(nerve C).σ i` is a smooth embedding
  (`IsLieGroupoid.isSmoothEmbedding_nerve_σ`);
* the leftmost-vertex projection `ComposableArrows.left`, the first-arrow projection, and the tail
  face map `(nerve C).δ 0` are submersions in every degree (`IsLieGroupoid.isSubmersion_nerve_left`,
  `IsLieGroupoid.isSubmersion_firstArrow`, `IsLieGroupoid.isSubmersion_nerve_δ_zero`).

## Main definitions

* `TauCeti.IsLieGroupoid.nerveDim`: recursive model dimension of `ComposableArrows C k`.
* `TauCeti.IsLieGroupoid.nerveChartedSpace`: `C^∞` manifold atlas on `ComposableArrows C k`.
* `TauCeti.IsLieGroupoid.zeroDiffeomorph`: `ComposableArrows C 0 ≃ₘ^∞ C`.
* `TauCeti.IsLieGroupoid.precompDiffeomorph`: recursive fibre-product diffeomorphism on
  `ComposableArrows C (k + 1)`.
* `TauCeti.IsLieGroupoid.oneDiffeomorph`: `ComposableArrows C 1 ≃ₘ^∞ Quiver.Total C`.

## References

* I. Moerdijk and J. Mrčun, *Introduction to Foliations and Lie Groupoids*, Cambridge Stud. Adv.
  Math. 91, Cambridge University Press (2003), Section 5.3.
* G. Segal, *Classifying spaces and spectral sequences*, Publ. Math. Inst. Hautes Études Sci. 34
  (1968), 105–112.
-/

public section

noncomputable section

open CategoryTheory Function Module Opposite Simplicial Topology
open scoped Manifold ContDiff

namespace TauCeti

namespace IsLieGroupoid

section NerveDim

/-- Model dimension of `ComposableArrows C k` for a Lie groupoid with object model space `E` and
arrow model space `E'`, defined recursively so that the inductive step matches the dimension of
`TauCeti.transverseFiberProductChartedSpace` syntactically. -/
def nerveDim (E E' : Type*) [AddCommGroup E] [Module ℝ E] [AddCommGroup E'] [Module ℝ E'] :
    ℕ → ℕ
  | 0 => finrank ℝ E + finrank ℝ E - finrank ℝ E
  | k + 1 => finrank ℝ E' + finrank ℝ (Fin (nerveDim E E' k) → ℝ) - finrank ℝ E

theorem nerveDim_zero (E E' : Type*) [AddCommGroup E] [Module ℝ E] [AddCommGroup E']
    [Module ℝ E'] : nerveDim E E' 0 = finrank ℝ E :=
  Nat.add_sub_cancel _ _

theorem nerveDim_succ (E E' : Type*) [AddCommGroup E] [Module ℝ E] [AddCommGroup E']
    [Module ℝ E'] (k : ℕ) :
    nerveDim E E' (k + 1) = finrank ℝ E' + nerveDim E E' k - finrank ℝ E := by
  simp [nerveDim]

end NerveDim

section SubmersionHelpers

private theorem isSubmersion_comp_diffeomorph
    {F₁ G₁ M₁ F₂ G₂ M₂ F₃ G₃ M₃ : Type*}
    [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁] [TopologicalSpace G₁]
    {I₁ : ModelWithCorners ℝ F₁ G₁} [I₁.Boundaryless]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [TopologicalSpace G₂]
    {I₂ : ModelWithCorners ℝ F₂ G₂}
    [NormedAddCommGroup F₃] [NormedSpace ℝ F₃] [FiniteDimensional ℝ F₃] [TopologicalSpace G₃]
    {I₃ : ModelWithCorners ℝ F₃ G₃}
    [TopologicalSpace M₁] [ChartedSpace G₁ M₁] [IsManifold I₁ ∞ M₁]
    [TopologicalSpace M₂] [ChartedSpace G₂ M₂]
    [TopologicalSpace M₃] [ChartedSpace G₃ M₃] [IsManifold I₃ ∞ M₃]
    {f : M₂ → M₃} (hf : Manifold.IsSubmersion I₂ I₃ ∞ f)
    (e : M₁ ≃ₘ^∞⟮I₁, I₂⟯ M₂) :
    Manifold.IsSubmersion I₁ I₃ ∞ (f ∘ e) := by
  refine ((hf.contMDiff.comp e.contMDiff).isSubmersionOfComplement_of_surjective_mfderiv (by simp)
    fun x ↦ ?_).isSubmersion
  rw [mfderiv_comp x (hf.contMDiff.mdifferentiableAt (by simp)) (e.mdifferentiable (by simp) x)]
  refine (hf.surjective_mfderiv (by simp) (e x)).comp ?_
  rw [← e.mfderivToContinuousLinearEquiv_coe (by simp)]
  exact (e.mfderivToContinuousLinearEquiv (by simp) x).surjective

private theorem isSubmersion_comp'
    {F₁ G₁ M₁ F₂ G₂ M₂ F₃ G₃ M₃ : Type*}
    [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁] [TopologicalSpace G₁]
    {I₁ : ModelWithCorners ℝ F₁ G₁} [I₁.Boundaryless]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [TopologicalSpace G₂]
    {I₂ : ModelWithCorners ℝ F₂ G₂}
    [NormedAddCommGroup F₃] [NormedSpace ℝ F₃] [FiniteDimensional ℝ F₃] [TopologicalSpace G₃]
    {I₃ : ModelWithCorners ℝ F₃ G₃}
    [TopologicalSpace M₁] [ChartedSpace G₁ M₁] [IsManifold I₁ ∞ M₁]
    [TopologicalSpace M₂] [ChartedSpace G₂ M₂]
    [TopologicalSpace M₃] [ChartedSpace G₃ M₃] [IsManifold I₃ ∞ M₃]
    {g : M₂ → M₃} {f : M₁ → M₂}
    (hg : Manifold.IsSubmersion I₂ I₃ ∞ g) (hf : Manifold.IsSubmersion I₁ I₂ ∞ f) :
    Manifold.IsSubmersion I₁ I₃ ∞ (g ∘ f) := by
  refine ((hg.contMDiff.comp hf.contMDiff).isSubmersionOfComplement_of_surjective_mfderiv (by simp)
    fun x ↦ ?_).isSubmersion
  rw [mfderiv_comp x (hg.contMDiff.mdifferentiableAt (by simp))
    (hf.contMDiff.mdifferentiableAt (by simp))]
  exact (hg.surjective_mfderiv (by simp) (f x)).comp (hf.surjective_mfderiv (by simp) x)

end SubmersionHelpers

section NerveManifold

variable {E H E' H' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
  (J : ModelWithCorners ℝ E' H') [J.Boundaryless]
  (C : Type*) [Category C] [IsGroupoid C]
  [TopologicalSpace C] [ChartedSpace H C] [IsManifold I ∞ C]
  [TopologicalSpace (Quiver.Total C)] [ChartedSpace H' (Quiver.Total C)]
  [IsManifold J ∞ (Quiver.Total C)]
  [hG : IsLieGroupoid I J C]

include hG

/-- Closed-form dimension of the `k`-simplex manifold `ComposableArrows C k` of a nonempty Lie
groupoid: `dim C + k * (dim(Quiver.Total C) - dim C)`. -/
theorem nerveDim_eq [Nonempty C] (k : ℕ) :
    nerveDim E E' k = finrank ℝ E + k * (finrank ℝ E' - finrank ℝ E) := by
  have hle := finrank_le_finrank I J C
  induction k with
  | zero => simp [nerveDim_zero]
  | succ k ih =>
    rw [nerveDim_succ, ih, Nat.add_one_mul]
    omega

private def NerveData (k : ℕ) : Type _ :=
  Σ' (cs : ChartedSpace (Fin (nerveDim E E' k) → ℝ) (ComposableArrows C k)),
    (letI := cs; IsManifold 𝓘(ℝ, Fin (nerveDim E E' k) → ℝ) ∞ (ComposableArrows C k)) ∧
    (letI := cs;
      Manifold.IsSubmersion 𝓘(ℝ, Fin (nerveDim E E' k) → ℝ) I ∞
        (ComposableArrows.left : ComposableArrows C k → C))

private def nerveZeroHomeomorph :
    ComposableArrows C 0 ≃ₜ {p : C × C // id p.1 = id p.2} :=
  letI := transverseFiberProductChartedSpace (f := (id : C → C)) (g := (id : C → C)) (n := ∞)
    (by simp) (contMDiff_id (I := I)) (contMDiff_id (I := I))
    (fun p _ ↦ transverse_id_right (id : C → C) p)
  (ComposableArrows.zeroHomeomorph (contMDiff_source I J C).continuous
    (contMDiff_unit (I := I) (J := J)).continuous).trans
    (transverseFiberProductIdRightDiffeomorph (n := ∞) (by simp)
      (contMDiff_id (I := I) (M := C))).symm.toHomeomorph

private theorem continuous_comp_nerve :
    Continuous fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦
      (⟨p.1.1.left, p.1.2.right, p.1.1.hom ≫ eqToHom p.2 ≫ p.1.2.hom⟩ : Quiver.Total C) := by
  let := composablePairsChartedSpace I J C
  exact (contMDiff_comp_composablePairs I J C).continuous.congr fun p ↦
    Quiver.Total.comp_def p.1.1 p.1.2 p.2

private def nerveDataZero : NerveData (E' := E') I C 0 := by
  letI cs₀_raw := transverseFiberProductChartedSpace (f := (id : C → C)) (g := (id : C → C))
    (n := ∞) (by simp) (contMDiff_id (I := I)) (contMDiff_id (I := I))
    (fun p _ ↦ transverse_id_right (id : C → C) p)
  letI cs₀ : ChartedSpace (Fin (nerveDim E E' 0) → ℝ) {p : C × C // id p.1 = id p.2} := cs₀_raw
  haveI hm₀ : IsManifold 𝓘(ℝ, Fin (nerveDim E E' 0) → ℝ) ∞ {p : C × C // id p.1 = id p.2} :=
    isManifold_transverseFiberProduct (f := (id : C → C)) (g := (id : C → C)) (n := ∞)
      (by simp) (contMDiff_id (I := I)) (contMDiff_id (I := I))
      (fun p _ ↦ transverse_id_right (id : C → C) p)
  let e₀ := nerveZeroHomeomorph I J C
  letI cs := e₀.pullbackChartedSpace (H := Fin (nerveDim E E' 0) → ℝ)
  haveI hm : IsManifold 𝓘(ℝ, Fin (nerveDim E E' 0) → ℝ) ∞ (ComposableArrows C 0) :=
    e₀.pullback_isManifold 𝓘(ℝ, Fin (nerveDim E E' 0) → ℝ) ∞
  let d : ComposableArrows C 0 ≃ₘ^∞⟮𝓘(ℝ, Fin (nerveDim E E' 0) → ℝ), I⟯ C :=
    (e₀.pullbackDiffeomorph 𝓘(ℝ, Fin (nerveDim E E' 0) → ℝ) ∞).trans
      (transverseFiberProductIdRightDiffeomorph (n := ∞) (by simp) (contMDiff_id (I := I) (M := C)))
  have hid : Manifold.IsSubmersion I I ∞ (id : C → C) :=
    (contMDiff_id.isSubmersionOfComplement_of_surjective_mfderiv (by simp) fun x ↦ by
      rw [mfderiv_id]; exact Function.surjective_id).isSubmersion
  have hsub : Manifold.IsSubmersion 𝓘(ℝ, Fin (nerveDim E E' 0) → ℝ) I ∞
      (ComposableArrows.left : ComposableArrows C 0 → C) := by
    convert isSubmersion_comp_diffeomorph hid d using 1
    funext F
    let d_id := transverseFiberProductIdRightDiffeomorph (n := ∞) (by simp)
      (contMDiff_id (I := I) (M := C))
    exact ((congrArg d_id (congrFun (e₀.coe_pullbackDiffeomorph
      𝓘(ℝ, Fin (nerveDim E E' 0) → ℝ) ∞) F)).trans
      ((congrArg (fun y ↦ d_id (d_id.symm.toHomeomorph y))
        (ComposableArrows.zeroHomeomorph_apply _ _ F)).trans
        (d_id.apply_symm_apply (F.obj 0)))).symm
  exact ⟨cs, hm, hsub⟩

private def nerveDataSucc (k : ℕ) (ih : NerveData (E' := E') I C k) :
    NerveData (E' := E') I C (k + 1) := by
  letI := ih.1
  haveI := ih.2.1
  letI cs_fp : ChartedSpace (Fin (nerveDim E E' (k + 1)) → ℝ)
      {p : Quiver.Total C × ComposableArrows C k // p.1.right = p.2.left} :=
    transverseFiberProductChartedSpace (f := (Quiver.Total.right : Quiver.Total C → C))
      (g := (ComposableArrows.left : ComposableArrows C k → C)) (n := ∞) (by simp)
      (contMDiff_target I J C) ih.2.2.contMDiff
      (fun p _ ↦ transverse_of_isSubmersion_left (isSubmersion_target I J C) (by simp) _ p)
  haveI hm_fp : IsManifold 𝓘(ℝ, Fin (nerveDim E E' (k + 1)) → ℝ) ∞
      {p : Quiver.Total C × ComposableArrows C k // p.1.right = p.2.left} :=
    isManifold_transverseFiberProduct (f := (Quiver.Total.right : Quiver.Total C → C))
      (g := (ComposableArrows.left : ComposableArrows C k → C)) (n := ∞) (by simp)
      (contMDiff_target I J C) ih.2.2.contMDiff
      (fun p _ ↦ transverse_of_isSubmersion_left (isSubmersion_target I J C) (by simp) _ p)
  have hsub_fst : Manifold.IsSubmersion 𝓘(ℝ, Fin (nerveDim E E' (k + 1)) → ℝ) J ∞
      (fun p : {p : Quiver.Total C × ComposableArrows C k // p.1.right = p.2.left} ↦ p.1.1) :=
    isSubmersion_fst_transverseFiberProduct (f := (Quiver.Total.right : Quiver.Total C → C))
      (g := (ComposableArrows.left : ComposableArrows C k → C)) (n := ∞) (by simp)
      (contMDiff_target I J C) ih.2.2.contMDiff
      (fun p _ ↦ transverse_of_isSubmersion_left (isSubmersion_target I J C) (by simp) _ p) ih.2.2
  let e_succ := ComposableArrows.precompHomeomorph (contMDiff_source I J C).continuous
    (contMDiff_unit (I := I) (J := J)).continuous (continuous_comp_nerve I J C) k
  letI cs := e_succ.pullbackChartedSpace (H := Fin (nerveDim E E' (k + 1)) → ℝ)
  haveI hm : IsManifold 𝓘(ℝ, Fin (nerveDim E E' (k + 1)) → ℝ) ∞ (ComposableArrows C (k + 1)) :=
    e_succ.pullback_isManifold 𝓘(ℝ, Fin (nerveDim E E' (k + 1)) → ℝ) ∞
  let d := e_succ.pullbackDiffeomorph 𝓘(ℝ, Fin (nerveDim E E' (k + 1)) → ℝ) ∞
  have hsub : Manifold.IsSubmersion 𝓘(ℝ, Fin (nerveDim E E' (k + 1)) → ℝ) I ∞
      (ComposableArrows.left : ComposableArrows C (k + 1) → C) := by
    convert isSubmersion_comp_diffeomorph
      (isSubmersion_comp' (isSubmersion_source (I := I) (J := J) (C := C)) hsub_fst) d using 1
    funext F
    dsimp only [Function.comp_apply, d, e_succ]
    rw [Homeomorph.coe_pullbackDiffeomorph,
      show ((ComposableArrows.precompHomeomorph (contMDiff_source I J C).continuous
        (contMDiff_unit (I := I) (J := J)).continuous (continuous_comp_nerve I J C) k F).val).1 =
        F.totalArrow 0 1 (Fin.zero_le _) from
        congrArg Prod.fst (ComposableArrows.precompHomeomorph_apply _ _ _ k F),
      ComposableArrows.totalArrow_left]
    rfl
  exact ⟨cs, hm, hsub⟩

private def nerveData : ∀ k : ℕ, NerveData (E' := E') I C k
  | 0 => nerveDataZero I J C
  | k + 1 => nerveDataSucc I J C k (nerveData k)

/-- The canonical `C^∞` charted-space structure on `ComposableArrows C k`, constructed recursively
from `C` in degree `0` and iterated transverse fibre products over `Quiver.Total.right` in higher
degrees. -/
@[instance_reducible]
def nerveChartedSpace (k : ℕ) :
    ChartedSpace (Fin (nerveDim E E' k) → ℝ) (ComposableArrows C k) :=
  (nerveData I J C k).1

/-- Each level `ComposableArrows C k` of the nerve of a Lie groupoid is a `C^∞` manifold. -/
theorem isManifold_nerve (k : ℕ) :
    letI := nerveChartedSpace I J C k
    IsManifold 𝓘(ℝ, Fin (nerveDim E E' k) → ℝ) ∞ (ComposableArrows C k) :=
  (nerveData I J C k).2.1

/-- The leftmost-vertex projection `ComposableArrows.left : ComposableArrows C k → C` is a
submersion in every degree `k`. -/
theorem isSubmersion_nerve_left (k : ℕ) :
    letI := nerveChartedSpace I J C k
    Manifold.IsSubmersion 𝓘(ℝ, Fin (nerveDim E E' k) → ℝ) I ∞
      (ComposableArrows.left : ComposableArrows C k → C) :=
  (nerveData I J C k).2.2

/-- The `0`-simplices of the smooth nerve are `C^∞` diffeomorphic to the object manifold `C`. -/
def zeroDiffeomorph :
    letI := nerveChartedSpace I J C 0
    ComposableArrows C 0 ≃ₘ^∞⟮𝓘(ℝ, Fin (nerveDim E E' 0) → ℝ), I⟯ C :=
  letI : ChartedSpace (Fin (nerveDim E E' 0) → ℝ) {p : C × C // id p.1 = id p.2} :=
    transverseFiberProductChartedSpace (f := (id : C → C)) (g := (id : C → C)) (n := ∞)
      (by simp) (contMDiff_id (I := I)) (contMDiff_id (I := I))
      (fun p _ ↦ transverse_id_right (id : C → C) p)
  letI := nerveChartedSpace I J C 0
  ((nerveZeroHomeomorph I J C).pullbackDiffeomorph 𝓘(ℝ, Fin (nerveDim E E' 0) → ℝ) ∞).trans
    (transverseFiberProductIdRightDiffeomorph (n := ∞) (by simp) (contMDiff_id (I := I) (M := C)))

@[simp]
theorem zeroDiffeomorph_apply (F : ComposableArrows C 0) :
    letI := nerveChartedSpace I J C 0
    zeroDiffeomorph I J C F = F.obj 0 :=
  letI cs₀_raw := transverseFiberProductChartedSpace (f := (id : C → C)) (g := (id : C → C))
    (n := ∞) (by simp) (contMDiff_id (I := I)) (contMDiff_id (I := I))
    (fun p _ ↦ transverse_id_right (id : C → C) p)
  letI : ChartedSpace (Fin (nerveDim E E' 0) → ℝ) {p : C × C // id p.1 = id p.2} := cs₀_raw
  letI := nerveChartedSpace I J C 0
  let d_id := transverseFiberProductIdRightDiffeomorph (n := ∞) (by simp)
    (contMDiff_id (I := I) (M := C))
  (congrArg d_id (congrFun ((nerveZeroHomeomorph I J C).coe_pullbackDiffeomorph
    𝓘(ℝ, Fin (nerveDim E E' 0) → ℝ) ∞) F)).trans
    ((congrArg (fun y ↦ d_id (d_id.symm.toHomeomorph y))
      (ComposableArrows.zeroHomeomorph_apply _ _ F)).trans (d_id.apply_symm_apply (F.obj 0)))

@[simp]
theorem zeroDiffeomorph_symm_apply (x : C) :
    letI := nerveChartedSpace I J C 0
    (zeroDiffeomorph I J C).symm x = ComposableArrows.mk₀ x :=
  letI := nerveChartedSpace I J C 0
  let d := zeroDiffeomorph I J C
  d.injective ((d.apply_symm_apply x).trans
    (zeroDiffeomorph_apply I J C (ComposableArrows.mk₀ x)).symm)

/-- The transverse fibre-product atlas on
`{p : Quiver.Total C × ComposableArrows C k // p.1.right = p.2.left}`. -/
@[instance_reducible]
def precompFiberProductChartedSpace (k : ℕ) :
    letI := nerveChartedSpace I J C k
    ChartedSpace (Fin (nerveDim E E' (k + 1)) → ℝ)
      {p : Quiver.Total C × ComposableArrows C k // p.1.right = p.2.left} :=
  letI := nerveChartedSpace I J C k
  haveI := isManifold_nerve I J C k
  transverseFiberProductChartedSpace (f := (Quiver.Total.right : Quiver.Total C → C))
    (g := (ComposableArrows.left : ComposableArrows C k → C)) (n := ∞) (by simp)
    (contMDiff_target I J C) (isSubmersion_nerve_left I J C k).contMDiff
    (fun p _ ↦ transverse_of_isSubmersion_left (isSubmersion_target I J C) (by simp) _ p)

theorem isManifold_precompFiberProduct (k : ℕ) :
    letI := nerveChartedSpace I J C k
    letI := precompFiberProductChartedSpace I J C k
    IsManifold 𝓘(ℝ, Fin (nerveDim E E' (k + 1)) → ℝ) ∞
      {p : Quiver.Total C × ComposableArrows C k // p.1.right = p.2.left} :=
  letI := nerveChartedSpace I J C k
  haveI := isManifold_nerve I J C k
  isManifold_transverseFiberProduct (f := (Quiver.Total.right : Quiver.Total C → C))
    (g := (ComposableArrows.left : ComposableArrows C k → C)) (n := ∞) (by simp)
    (contMDiff_target I J C) (isSubmersion_nerve_left I J C k).contMDiff
    (fun p _ ↦ transverse_of_isSubmersion_left (isSubmersion_target I J C) (by simp) _ p)

theorem isSmoothEmbedding_coe_precompFiberProduct (k : ℕ) :
    letI := nerveChartedSpace I J C k
    letI := precompFiberProductChartedSpace I J C k
    Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin (nerveDim E E' (k + 1)) → ℝ)
      (J.prod 𝓘(ℝ, Fin (nerveDim E E' k) → ℝ)) ∞
      (Subtype.val :
        {p : Quiver.Total C × ComposableArrows C k // p.1.right = p.2.left} →
          Quiver.Total C × ComposableArrows C k) :=
  letI := nerveChartedSpace I J C k
  haveI := isManifold_nerve I J C k
  isSmoothEmbedding_coe_transverseFiberProduct (f := (Quiver.Total.right : Quiver.Total C → C))
    (g := (ComposableArrows.left : ComposableArrows C k → C)) (n := ∞) (by simp)
    (contMDiff_target I J C) (isSubmersion_nerve_left I J C k).contMDiff
    (fun p _ ↦ transverse_of_isSubmersion_left (isSubmersion_target I J C) (by simp) _ p)

/-- Splitting a `(k + 1)`-simplex into its first arrow and the remaining `k`-simplex is a `C^∞`
diffeomorphism onto the transverse fibre product over `Quiver.Total.right` and
`ComposableArrows.left`. -/
def precompDiffeomorph (k : ℕ) :
    letI := nerveChartedSpace I J C k
    letI := precompFiberProductChartedSpace I J C k
    letI := nerveChartedSpace I J C (k + 1)
    ComposableArrows C (k + 1) ≃ₘ^∞⟮
      𝓘(ℝ, Fin (nerveDim E E' (k + 1)) → ℝ),
      𝓘(ℝ, Fin (nerveDim E E' (k + 1)) → ℝ)⟯
      {p : Quiver.Total C × ComposableArrows C k // p.1.right = p.2.left} :=
  letI := nerveChartedSpace I J C k
  letI := precompFiberProductChartedSpace I J C k
  (ComposableArrows.precompHomeomorph (contMDiff_source I J C).continuous
    (contMDiff_unit (I := I) (J := J)).continuous (continuous_comp_nerve I J C)
    k).pullbackDiffeomorph 𝓘(ℝ, Fin (nerveDim E E' (k + 1)) → ℝ) ∞

@[simp]
theorem coe_precompDiffeomorph_apply (k : ℕ) (F : ComposableArrows C (k + 1)) :
    letI := nerveChartedSpace I J C k
    letI := precompFiberProductChartedSpace I J C k
    letI := nerveChartedSpace I J C (k + 1)
    (precompDiffeomorph I J C k F).val = (F.totalArrow 0 1 (Fin.zero_le _), F.δ₀) :=
  letI := nerveChartedSpace I J C k
  letI := precompFiberProductChartedSpace I J C k
  (congrArg Subtype.val (congrFun ((ComposableArrows.precompHomeomorph
    (contMDiff_source I J C).continuous (contMDiff_unit (I := I) (J := J)).continuous
    (continuous_comp_nerve I J C) k).coe_pullbackDiffeomorph
    𝓘(ℝ, Fin (nerveDim E E' (k + 1)) → ℝ) ∞) F)).trans
    (ComposableArrows.precompHomeomorph_apply _ _ _ k F)

@[simp]
theorem precompDiffeomorph_symm_apply (k : ℕ)
    (p : {p : Quiver.Total C × ComposableArrows C k // p.1.right = p.2.left}) :
    letI := nerveChartedSpace I J C k
    letI := precompFiberProductChartedSpace I J C k
    letI := nerveChartedSpace I J C (k + 1)
    (precompDiffeomorph I J C k).symm p = p.1.2.precomp (p.1.1.hom ≫ eqToHom p.2) :=
  letI := nerveChartedSpace I J C k
  letI := precompFiberProductChartedSpace I J C k
  (congrFun ((ComposableArrows.precompHomeomorph
    (contMDiff_source I J C).continuous (contMDiff_unit (I := I) (J := J)).continuous
    (continuous_comp_nerve I J C) k).coe_pullbackDiffeomorph_symm
    𝓘(ℝ, Fin (nerveDim E E' (k + 1)) → ℝ) ∞) p).trans
    (ComposableArrows.precompHomeomorph_symm_apply _ _ _ k p)

/-! ### Smoothness of total arrows and universal property of the nerve manifold -/

private theorem contMDiff_precomp_totalArrow (k : ℕ)
    (ih : letI := nerveChartedSpace I J C k
      ∀ i j (hij : i ≤ j), ContMDiff 𝓘(ℝ, Fin (nerveDim E E' k) → ℝ) J ∞
        (fun F : ComposableArrows C k ↦ F.totalArrow i j hij))
    (i j : Fin (k + 2)) (hij : i ≤ j) :
    letI := nerveChartedSpace I J C k
    letI := precompFiberProductChartedSpace I J C k
    ContMDiff 𝓘(ℝ, Fin (nerveDim E E' (k + 1)) → ℝ) J ∞
      (fun p : {p : Quiver.Total C × ComposableArrows C k // p.1.right = p.2.left} ↦
        (p.1.2.precomp (p.1.1.hom ≫ eqToHom p.2)).totalArrow i j hij) := by
  let := nerveChartedSpace I J C k
  let := precompFiberProductChartedSpace I J C k
  let := composablePairsChartedSpace I J C
  have := isManifold_nerve I J C k
  have := isManifold_precompFiberProduct I J C k
  have := isManifold_composablePairs I J C
  have hemb := isSmoothEmbedding_coe_precompFiberProduct I J C k
  have ha := contMDiff_fst.comp hemb.contMDiff
  have hF := contMDiff_snd.comp hemb.contMDiff
  rcases i with ⟨_ | i, hi⟩
  · rcases j with ⟨_ | _ | j, hj⟩
    · simpa only [Function.comp_def, ComposableArrows.totalArrow_def,
        ComposableArrows.precomp, ComposableArrows.Precomp.obj, ComposableArrows.Precomp.map] using
        (contMDiff_unit (I := I) (J := J)).comp ((contMDiff_source I J C).comp ha)
    · convert ha using 1
      funext p
      exact ComposableArrows.totalArrow_precomp_zero_one p.1.1 p.1.2 p.2
    · have ht := (ih ⟨0, by omega⟩ ⟨j + 1, by omega⟩ (Nat.zero_le _)).comp hF
      let pair : {p : Quiver.Total C × ComposableArrows C k // p.1.right = p.2.left} →
          {q : Quiver.Total C × Quiver.Total C // q.1.right = q.2.left} :=
        fun p ↦ ⟨(p.1.1, p.1.2.totalArrow ⟨0, by omega⟩ ⟨j + 1, by omega⟩ (Nat.zero_le _)),
          by simpa only [ComposableArrows.totalArrow_left] using p.2⟩
      have hpair := ((isSmoothEmbedding_coe_composablePairs I J C).contMDiff_iff_comp
        (f := pair)).2 (ha.prodMk ht)
      convert (contMDiff_comp_composablePairs I J C).comp hpair using 1
      funext p
      have hpair_eq : pair p = ⟨(p.1.1, ⟨p.1.2.obj ⟨0, by omega⟩, p.1.2.obj ⟨j + 1, by omega⟩,
          p.1.2.map (homOfLE (Nat.zero_le _))⟩), p.2⟩ :=
        Subtype.ext (Prod.ext rfl (ComposableArrows.totalArrow_def p.1.2
          ⟨0, by omega⟩ ⟨j + 1, by omega⟩ (Nat.zero_le _)))
      conv_lhs => simp only [Fin.zero_eta]
      rw [ComposableArrows.totalArrow_precomp_zero_succ_succ p.1.2 (p.1.1.hom ≫ eqToHom p.2) j
        (by omega), Function.comp_apply, hpair_eq, Quiver.Total.comp_def, Category.assoc]
  · rcases j with ⟨_ | j, hj⟩
    · simp only [Fin.mk_le_mk] at hij; omega
    · convert (ih ⟨i, by omega⟩ ⟨j, by omega⟩ (by simp only [Fin.mk_le_mk] at hij ⊢; omega)).comp
        hF using 1
      funext p
      exact ComposableArrows.totalArrow_precomp_succ_succ p.1.2 (p.1.1.hom ≫ eqToHom p.2)
        ⟨i, by omega⟩ ⟨j, by omega⟩ (by simp only [Fin.mk_le_mk] at hij ⊢; omega)

/-- Every arrow `F.totalArrow i j hij` of a `k`-simplex depends smoothly on `F`. -/
theorem contMDiff_totalArrow (k : ℕ) (i j : Fin (k + 1)) (hij : i ≤ j) :
    letI := nerveChartedSpace I J C k
    ContMDiff 𝓘(ℝ, Fin (nerveDim E E' k) → ℝ) J ∞
      (fun F : ComposableArrows C k ↦ F.totalArrow i j hij) := by
  induction k with
  | zero =>
    let := nerveChartedSpace I J C 0
    have hi : i = 0 := by omega
    have hj : j = 0 := by omega
    subst hi hj
    convert (contMDiff_unit (I := I) (J := J) (C := C)).comp (zeroDiffeomorph I J C).contMDiff
      using 1
    funext F
    rw [Function.comp_apply, zeroDiffeomorph_apply]
    exact ComposableArrows.totalArrow_self F 0
  | succ k ih =>
    let := nerveChartedSpace I J C k
    let := precompFiberProductChartedSpace I J C k
    let := nerveChartedSpace I J C (k + 1)
    rw [← (precompDiffeomorph I J C k).symm.contMDiff_comp_diffeomorph_iff le_rfl]
    exact (contMDiff_precomp_totalArrow I J C k ih i j hij).congr fun p ↦ by
      simp only [Function.comp_apply, precompDiffeomorph_symm_apply]

/-- Every vertex `F.obj i` of a `k`-simplex depends smoothly on `F`. -/
theorem contMDiff_nerve_obj (k : ℕ) (i : Fin (k + 1)) :
    letI := nerveChartedSpace I J C k
    ContMDiff 𝓘(ℝ, Fin (nerveDim E E' k) → ℝ) I ∞
      (fun F : ComposableArrows C k ↦ F.obj i) := by
  let := nerveChartedSpace I J C k
  simpa only [Function.comp_def, ComposableArrows.totalArrow_left] using
    (contMDiff_source I J C).comp (contMDiff_totalArrow I J C k i i le_rfl)

/-- A map from any charted space into `ComposableArrows C k` is `C^∞` if and only if each total
arrow `(f x).totalArrow i j hij` depends `C^∞` on `x`. -/
theorem contMDiff_nerve_iff {EM HM M : Type*}
    [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
    {IM : ModelWithCorners ℝ EM HM} [TopologicalSpace M] [ChartedSpace HM M]
    {k : ℕ} {f : M → ComposableArrows C k} :
    letI := nerveChartedSpace I J C k
    ContMDiff IM 𝓘(ℝ, Fin (nerveDim E E' k) → ℝ) ∞ f ↔
      ∀ i j (hij : i ≤ j), ContMDiff IM J ∞ (fun x ↦ (f x).totalArrow i j hij) := by
  let := nerveChartedSpace I J C k
  refine ⟨fun hf i j hij ↦ (contMDiff_totalArrow I J C k i j hij).comp hf, ?_⟩
  induction k with
  | zero =>
    let := nerveChartedSpace I J C 0
    intro h
    rw [← (zeroDiffeomorph I J C).contMDiff_diffeomorph_comp_iff le_rfl]
    exact ((contMDiff_source I J C).comp (h 0 0 le_rfl)).congr fun x ↦ by
      simp only [Function.comp_apply, zeroDiffeomorph_apply, ComposableArrows.totalArrow_left]
  | succ k ih =>
    let := nerveChartedSpace I J C k
    let := precompFiberProductChartedSpace I J C k
    let := nerveChartedSpace I J C (k + 1)
    intro h
    rw [← (precompDiffeomorph I J C k).contMDiff_diffeomorph_comp_iff le_rfl]
    refine ((isSmoothEmbedding_coe_precompFiberProduct I J C k).contMDiff_iff_comp
      (f := precompDiffeomorph I J C k ∘ f)).2 ?_
    have htail : ContMDiff IM 𝓘(ℝ, Fin (nerveDim E E' k) → ℝ) ∞ (fun x ↦ (f x).δ₀) :=
      ih fun i j hij ↦ (h i.succ j.succ (Fin.succ_le_succ_iff.2 hij)).congr fun x ↦
        (f x).totalArrow_whiskerLeft (Fin.succFunctor (k + 1)) i j hij
    convert (h 0 1 (Fin.zero_le _)).prodMk htail using 1
    funext x
    exact coe_precompDiffeomorph_apply I J C k (f x)

/-! ### Smoothness of simplicial operators, embeddings of degeneracies, and submersions -/

/-- Reindexing strings of composable arrows along any poset functor `Fin (k + 1) ⥤ Fin (m + 1)` is
smooth. -/
theorem contMDiff_whiskerLeft {m k : ℕ} (Φ : Fin (k + 1) ⥤ Fin (m + 1)) :
    letI := nerveChartedSpace I J C m
    letI := nerveChartedSpace I J C k
    ContMDiff 𝓘(ℝ, Fin (nerveDim E E' m) → ℝ) 𝓘(ℝ, Fin (nerveDim E E' k) → ℝ) ∞
      (fun F : ComposableArrows C m ↦ F.whiskerLeft Φ) :=
  letI := nerveChartedSpace I J C m
  letI := nerveChartedSpace I J C k
  (contMDiff_nerve_iff I J C).2 fun i j hij ↦ by
    simpa only [ComposableArrows.totalArrow_whiskerLeft] using
      contMDiff_totalArrow I J C m (Φ.obj i) (Φ.obj j) (Φ.monotone hij)

/-- Every simplicial operator of the nerve of a Lie groupoid is smooth. -/
theorem contMDiff_nerve_map {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') :
    letI := nerveChartedSpace I J C Δ.unop.len
    letI := nerveChartedSpace I J C Δ'.unop.len
    ContMDiff (M := ComposableArrows C Δ.unop.len) (M' := ComposableArrows C Δ'.unop.len)
      𝓘(ℝ, Fin (nerveDim E E' Δ.unop.len) → ℝ)
      𝓘(ℝ, Fin (nerveDim E E' Δ'.unop.len) → ℝ) ∞ ((nerve C).map f) :=
  contMDiff_whiskerLeft I J C (SimplexCategory.toCat.map f.unop).toFunctor

/-- Every face map `(nerve C).δ i` of the nerve of a Lie groupoid is smooth. -/
theorem contMDiff_nerve_δ (k : ℕ) (i : Fin (k + 2)) :
    letI := nerveChartedSpace I J C (k + 1)
    letI := nerveChartedSpace I J C k
    ContMDiff (M := ComposableArrows C (k + 1)) (M' := ComposableArrows C k)
      𝓘(ℝ, Fin (nerveDim E E' (k + 1)) → ℝ) 𝓘(ℝ, Fin (nerveDim E E' k) → ℝ) ∞
      ((nerve C).δ i) :=
  contMDiff_nerve_map I J C (SimplexCategory.δ i).op

/-- Every degeneracy map `(nerve C).σ i` of the nerve of a Lie groupoid is smooth. -/
theorem contMDiff_nerve_σ (k : ℕ) (i : Fin (k + 1)) :
    letI := nerveChartedSpace I J C k
    letI := nerveChartedSpace I J C (k + 1)
    ContMDiff (M := ComposableArrows C k) (M' := ComposableArrows C (k + 1))
      𝓘(ℝ, Fin (nerveDim E E' k) → ℝ) 𝓘(ℝ, Fin (nerveDim E E' (k + 1)) → ℝ) ∞
      ((nerve C).σ i) :=
  contMDiff_nerve_map I J C (SimplexCategory.σ i).op

/-- Every degeneracy map `(nerve C).σ i` of a Lie groupoid is a smooth embedding, since the face
map `(nerve C).δ i.castSucc` is a smooth left inverse. -/
theorem isSmoothEmbedding_nerve_σ (k : ℕ) (i : Fin (k + 1)) :
    letI := nerveChartedSpace I J C k
    letI := nerveChartedSpace I J C (k + 1)
    Manifold.IsSmoothEmbedding (M := ComposableArrows C k) (N := ComposableArrows C (k + 1))
      𝓘(ℝ, Fin (nerveDim E E' k) → ℝ) 𝓘(ℝ, Fin (nerveDim E E' (k + 1)) → ℝ) ∞
      ((nerve C).σ i) := by
  let := nerveChartedSpace I J C k
  let := nerveChartedSpace I J C (k + 1)
  have := isManifold_nerve I J C k
  have := isManifold_nerve I J C (k + 1)
  exact (contMDiff_nerve_σ I J C k i).isSmoothEmbedding_of_leftInverse (by simp)
    ((contMDiff_nerve_δ I J C k i.castSucc).of_le (by simp)) ((nerve C).δ_comp_σ_self_apply i)

/-- Projecting a `(k + 1)`-simplex onto its first arrow is a submersion in every degree `k`. -/
theorem isSubmersion_firstArrow (k : ℕ) :
    letI := nerveChartedSpace I J C (k + 1)
    Manifold.IsSubmersion 𝓘(ℝ, Fin (nerveDim E E' (k + 1)) → ℝ) J ∞
      (fun F : ComposableArrows C (k + 1) ↦ F.totalArrow 0 1 (Fin.zero_le _)) := by
  let := nerveChartedSpace I J C k
  let := precompFiberProductChartedSpace I J C k
  let := nerveChartedSpace I J C (k + 1)
  have := isManifold_nerve I J C k
  have := isManifold_precompFiberProduct I J C k
  have := isManifold_nerve I J C (k + 1)
  have hsub : Manifold.IsSubmersion 𝓘(ℝ, Fin (nerveDim E E' (k + 1)) → ℝ) J ∞
      (fun p : {p : Quiver.Total C × ComposableArrows C k // p.1.right = p.2.left} ↦ p.1.1) :=
    isSubmersion_fst_transverseFiberProduct
      (f := (Quiver.Total.right : Quiver.Total C → C))
      (g := (ComposableArrows.left : ComposableArrows C k → C)) (n := ∞) (by simp)
      (contMDiff_target I J C) (isSubmersion_nerve_left I J C k).contMDiff
      (fun p _ ↦ transverse_of_isSubmersion_left (isSubmersion_target I J C) (by simp) _ p)
      (isSubmersion_nerve_left I J C k)
  convert isSubmersion_comp_diffeomorph hsub (precompDiffeomorph I J C k) using 1
  funext F
  exact (congrArg Prod.fst (coe_precompDiffeomorph_apply I J C k F)).symm

/-- The `0`-th face map `(nerve C).δ 0 : ComposableArrows C (k + 1) → ComposableArrows C k`
(dropping the first vertex) is a submersion in every degree `k`. -/
theorem isSubmersion_nerve_δ_zero (k : ℕ) :
    letI := nerveChartedSpace I J C (k + 1)
    letI := nerveChartedSpace I J C k
    Manifold.IsSubmersion (M := ComposableArrows C (k + 1)) (N := ComposableArrows C k)
      𝓘(ℝ, Fin (nerveDim E E' (k + 1)) → ℝ) 𝓘(ℝ, Fin (nerveDim E E' k) → ℝ) ∞
      ((nerve C).δ 0) := by
  let := nerveChartedSpace I J C k
  let := precompFiberProductChartedSpace I J C k
  let := nerveChartedSpace I J C (k + 1)
  have := isManifold_nerve I J C k
  have := isManifold_precompFiberProduct I J C k
  have := isManifold_nerve I J C (k + 1)
  have hsub : Manifold.IsSubmersion 𝓘(ℝ, Fin (nerveDim E E' (k + 1)) → ℝ)
      𝓘(ℝ, Fin (nerveDim E E' k) → ℝ) ∞
      (fun p : {p : Quiver.Total C × ComposableArrows C k // p.1.right = p.2.left} ↦ p.1.2) :=
    isSubmersion_snd_transverseFiberProduct
      (f := (Quiver.Total.right : Quiver.Total C → C))
      (g := (ComposableArrows.left : ComposableArrows C k → C)) (n := ∞) (by simp)
      (contMDiff_target I J C) (isSubmersion_nerve_left I J C k).contMDiff
      (fun p _ ↦ transverse_of_isSubmersion_left (isSubmersion_target I J C) (by simp) _ p)
      (isSubmersion_target I J C)
  change Manifold.IsSubmersion _ _ ∞ (fun F : ComposableArrows C (k + 1) ↦ F.δ₀)
  convert isSubmersion_comp_diffeomorph hsub (precompDiffeomorph I J C k) using 1
  funext F
  exact (congrArg Prod.snd (coe_precompDiffeomorph_apply I J C k F)).symm

/-- The `1`-simplices of the smooth nerve are `C^∞` diffeomorphic to the total-arrow manifold
`Quiver.Total C`. -/
def oneDiffeomorph :
    letI := nerveChartedSpace I J C 1
    ComposableArrows C 1 ≃ₘ^∞⟮𝓘(ℝ, Fin (nerveDim E E' 1) → ℝ), J⟯ Quiver.Total C :=
  letI := nerveChartedSpace I J C 1
  { toFun := fun F ↦ F.totalArrow 0 1 (Fin.zero_le _)
    invFun := fun a ↦ ComposableArrows.mk₁ a.hom
    left_inv := fun F ↦ by
      dsimp only
      rw [ComposableArrows.totalArrow_def]
      exact ComposableArrows.mk₁_hom F
    right_inv := fun ⟨x, y, f⟩ ↦ by
      dsimp only
      rw [ComposableArrows.totalArrow_def]
      rfl
    contMDiff_toFun := contMDiff_totalArrow I J C 1 0 1 (Fin.zero_le _)
    contMDiff_invFun := (contMDiff_nerve_iff I J C).2 fun i j hij ↦ by
      fin_cases i <;> fin_cases j
      · convert (contMDiff_unit (I := I) (J := J)).comp (contMDiff_source I J C) using 1
        funext ⟨x, y, f⟩
        exact ComposableArrows.totalArrow_self (ComposableArrows.mk₁ f) 0
      · convert contMDiff_id (I := J) using 1
        funext ⟨x, y, f⟩
        rw [ComposableArrows.totalArrow_def]
        rfl
      · exact absurd hij (by decide)
      · convert (contMDiff_unit (I := I) (J := J)).comp (contMDiff_target I J C) using 1
        funext ⟨x, y, f⟩
        exact ComposableArrows.totalArrow_self (ComposableArrows.mk₁ f) 1 }

@[simp]
theorem oneDiffeomorph_apply (F : ComposableArrows C 1) :
    letI := nerveChartedSpace I J C 1
    oneDiffeomorph I J C F = F.totalArrow 0 1 (Fin.zero_le _) :=
  (rfl)

@[simp]
theorem oneDiffeomorph_symm_apply (a : Quiver.Total C) :
    letI := nerveChartedSpace I J C 1
    (oneDiffeomorph I J C).symm a = ComposableArrows.mk₁ a.hom :=
  (rfl)

/-- Each level `ComposableArrows C k` of the nerve of a Lie groupoid is second-countable. -/
theorem secondCountableTopology_nerve (k : ℕ) :
    SecondCountableTopology (ComposableArrows C k) := by
  have := secondCountableTopology_objects I J C
  have := secondCountableTopology_arrows (I := I) (J := J) (C := C)
  induction k with
  | zero =>
    exact (ComposableArrows.zeroHomeomorph (contMDiff_source I J C).continuous
      (contMDiff_unit (I := I) (J := J)).continuous).isEmbedding.secondCountableTopology
  | succ k ih =>
    have : SecondCountableTopology
        {p : Quiver.Total C × ComposableArrows C k // p.1.right = p.2.left} :=
      Topology.IsEmbedding.subtypeVal.secondCountableTopology
    exact (ComposableArrows.precompHomeomorph (contMDiff_source I J C).continuous
      (contMDiff_unit (I := I) (J := J)).continuous (continuous_comp_nerve I J C)
      k).isEmbedding.secondCountableTopology

end NerveManifold

end IsLieGroupoid

end TauCeti
