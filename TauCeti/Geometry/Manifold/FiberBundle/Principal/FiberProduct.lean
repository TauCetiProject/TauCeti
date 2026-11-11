/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberBundle.Principal
public import TauCeti.Geometry.Manifold.FiberBundle.Submersion
public import TauCeti.Geometry.Manifold.FiberProduct.Manifold
public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# The self-fibre product of a smooth principal bundle

The equal-projection subtype of the product of two principal total spaces carries the
transverse fibre-product atlas. The principal action identifies this manifold with `P × G`
by `(p,g) ↦ (p,p·g)`. Its inverse records the first point and the division element.
In particular division is smooth on the actual self-fibre product, with its inherited topology.

We use `TauCeti.transverseFiberProductChartedSpace`, rather than transporting an atlas along
the action. Thus this comparison identifies the independently constructed embedded manifold
with the principal product model. No separation or countability hypotheses are needed.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*,
  Springer (1993), §§10.2–10.3 (principal bundles and division).
* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer (2013),
  Theorem 6.30 (transverse fibre products).
-/

public section

open Bundle MulOpposite
open scoped Manifold ContDiff

namespace TauCeti.PrincipalBundle

variable {B G : Type*} {P : B → Type*} [TopologicalSpace (TotalSpace G P)]

local notation "T" => ManifoldTotalSpace G P
local notation "ι" => ManifoldTotalSpace.homeomorph G P
local notation "π₀" => fun p : T ↦ Bundle.TotalSpace.proj
  (Homeomorph.symm (ManifoldTotalSpace.homeomorph G P) p)
local notation "R" => {z : T × T // π₀ (Prod.fst z) = π₀ (Prod.snd z)}

-- Transport only the fibre element; the total-space point remains unchanged.
private def secondInFirstFiber (z : R) : P (π₀ z.1.1) :=
  cast (congrArg P z.2.symm) ((ι).symm z.1.2).2

private theorem totalSpaceMk_secondInFirstFiber (z : R) :
    ι ⟨π₀ z.1.1, secondInFirstFiber z⟩ = z.1.2 := by
  exact (congrArg ι (TotalSpace.mk_cast z.2.symm ((ι).symm z.1.2).2)).trans
    ((ι).apply_symm_apply z.1.2)

variable [TopologicalSpace B] [Group G] [TopologicalSpace G]
  [∀ b, TopologicalSpace (P b)] [FiberBundle G P]
  [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]

/-- Division on the equal-projection subtype: the unique group element taking the first
point to the second by the principal right action. -/
noncomputable def fiberProductDivision (z : R) : G :=
  division G ((ι).symm z.1.1).2 (secondInFirstFiber z)

/-- On a pair in a displayed common fibre, division is the original fibrewise division. -/
@[simp]
theorem fiberProductDivision_mk {b : B} (p q : P b) :
    fiberProductDivision (⟨(ι ⟨b, p⟩, ι ⟨b, q⟩), by simp⟩ : R) = division G p q := by
  rw [fiberProductDivision, division_eq_iff]
  apply TotalSpace.mk_injective _
  apply (ι).injective
  rw [totalSpaceMk_secondInFirstFiber, ← ManifoldTotalSpace.smul_homeomorph]
  simp only [Homeomorph.apply_symm_apply, ManifoldTotalSpace.smul_homeomorph, smul_division]

/-- Division is characterized by the equation for the principal right action. -/
theorem fiberProductDivision_eq_iff (z : R) {g : G} :
    fiberProductDivision z = g ↔ op g • z.1.1 = z.1.2 := by
  rw [fiberProductDivision, division_eq_iff]
  constructor
  · intro h
    have h' := congrArg (fun p ↦ ι ⟨π₀ z.1.1, p⟩) h
    rw [← ManifoldTotalSpace.smul_homeomorph, Homeomorph.apply_symm_apply,
      totalSpaceMk_secondInFirstFiber] at h'
    exact h'
  · intro h
    apply TotalSpace.mk_injective _
    apply (ι).injective
    rw [← ManifoldTotalSpace.smul_homeomorph, Homeomorph.apply_symm_apply,
      totalSpaceMk_secondInFirstFiber]
    exact h

/-- The division element sends the first point of a same-base pair to the second. -/
@[simp]
theorem op_fiberProductDivision_smul (z : R) :
    op (fiberProductDivision z) • z.1.1 = z.1.2 :=
  (fiberProductDivision_eq_iff z).1 rfl

section Smooth

variable {EB HB EG HG : Type*}
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
  {IB : ModelWithCorners ℝ EB HB} {IG : ModelWithCorners ℝ EG HG}
  [ChartedSpace HB B] [ChartedSpace HG G] {n : ℕ∞ω}
  [IsManifold IB n B] [LieGroup IG n G] [ContMDiffFiberBundle n G P IB IG]
  [IB.Boundaryless] [IG.Boundaryless]
  [FiniteDimensional ℝ EB] [FiniteDimensional ℝ EG]

omit [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  [IB.Boundaryless] [IG.Boundaryless]
  [FiniteDimensional ℝ EB] [FiniteDimensional ℝ EG] in
private theorem self_transverse (hn : 1 ≤ n) (z : T × T) (_ : π₀ z.1 = π₀ z.2) :
    (mfderiv (IB.prod IG) IB π₀ z.1).range ⊔
      (((tangentSpaceCast IB (π₀ z.2) (π₀ z.1)).toContinuousLinearMap).comp
        (mfderiv (IB.prod IG) IB π₀ z.2)).range = ⊤ := by
  have h := (ManifoldTotalSpace.isSubmersion_proj n G P IB IG).surjective_mfderiv
    (ne_of_gt (lt_of_lt_of_le zero_lt_one hn)) z.1
  rw [LinearMap.range_eq_top.2 h, top_sup_eq]

local notation "K" => 𝓘(ℝ, Fin (Module.finrank ℝ (EB × EG) +
  Module.finrank ℝ (EB × EG) - Module.finrank ℝ EB) → ℝ)

/-- The transverse fibre-product atlas on the equal-projection subtype of a principal bundle.
It retains the subspace topology; the atlas is named rather than a global instance. -/
@[instance_reducible]
noncomputable def fiberProductChartedSpace (hn : 1 ≤ n) :
    ChartedSpace (Fin (Module.finrank ℝ (EB × EG) +
      Module.finrank ℝ (EB × EG) - Module.finrank ℝ EB) → ℝ) R :=
  transverseFiberProductChartedSpace hn
    (ManifoldTotalSpace.contMDiff_proj n G P IB IG)
    (ManifoldTotalSpace.contMDiff_proj n G P IB IG)
    (self_transverse (G := G) (P := P) (IG := IG) hn)

variable (hn : 1 ≤ n)

omit [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P] in
/-- The self-fibre product with its transverse atlas is a `C^n` manifold. -/
theorem isManifold_fiberProduct :
    letI := fiberProductChartedSpace (G := G) (P := P) (IB := IB) (IG := IG) hn
    IsManifold K n R :=
  isManifold_transverseFiberProduct hn
    (ManifoldTotalSpace.contMDiff_proj n G P IB IG)
    (ManifoldTotalSpace.contMDiff_proj n G P IB IG)
    (self_transverse (G := G) (P := P) (IG := IG) hn)

omit [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P] in
/-- The inclusion of the principal self-fibre product into the product of total spaces is
a smooth embedding. -/
theorem isSmoothEmbedding_fiberProduct :
    letI := fiberProductChartedSpace (G := G) (P := P) (IB := IB) (IG := IG) hn
    Manifold.IsSmoothEmbedding K ((IB.prod IG).prod (IB.prod IG)) n
      (Subtype.val : R → T × T) :=
  isSmoothEmbedding_coe_transverseFiberProduct hn
    (ManifoldTotalSpace.contMDiff_proj n G P IB IG)
    (ManifoldTotalSpace.contMDiff_proj n G P IB IG)
    (self_transverse (G := G) (P := P) (IG := IG) hn)

/-- Division is `C^n` on the actual principal self-fibre-product manifold. -/
theorem contMDiff_fiberProductDivision :
    letI := fiberProductChartedSpace (G := G) (P := P) (IB := IB) (IG := IG) hn
    ContMDiff K IG n (fiberProductDivision (G := G) (P := P)) := by
  let := fiberProductChartedSpace (G := G) (P := P) (IB := IB) (IG := IG) hn
  have h := (isSmoothEmbedding_fiberProduct (G := G) (P := P) (IB := IB) (IG := IG) hn).contMDiff
  have hp := contMDiff_fst.comp h
  have hq := contMDiff_snd.comp h
  have hp' : ContMDiff K (IB.prod IG) n
      (fun z : R ↦ ι ⟨π₀ z.1.1, ((ι).symm z.1.1).2⟩) := by
    simpa only [TotalSpace.eta, Homeomorph.apply_symm_apply, Function.comp_def] using hp
  have hq' : ContMDiff K (IB.prod IG) n
      (fun z : R ↦ ι ⟨π₀ z.1.1, secondInFirstFiber z⟩) := by
    simpa only [totalSpaceMk_secondInFirstFiber, Function.comp_def] using hq
  exact hp'.division hq'

/-- The principal action identifies `P × G` diffeomorphically with the self-fibre product,
endowed with its transverse atlas. The inverse is first projection paired with division. -/
noncomputable def actionDiffeomorph :
    letI := fiberProductChartedSpace (G := G) (P := P) (IB := IB) (IG := IG) hn
    Diffeomorph ((IB.prod IG).prod IG) K (T × G) R n := by
  letI := fiberProductChartedSpace (G := G) (P := P) (IB := IB) (IG := IG) hn
  exact {
    toFun x := ⟨(x.1, op x.2 • x.1), by
      simp only [ManifoldTotalSpace.homeomorph_symm_smul]⟩
    invFun z := (z.1.1, fiberProductDivision z)
    left_inv x := by
      obtain ⟨⟨b, p⟩, hp⟩ := (ι).surjective x.1
      rcases x with ⟨x, g⟩
      dsimp at hp
      subst x
      simp
    right_inv z := by
      apply Subtype.ext
      exact Prod.ext rfl (op_fiberProductDivision_smul z)
    contMDiff_toFun := by
      have := isManifold_fiberProduct (G := G) (P := P) (IB := IB) (IG := IG) hn
      have he := isSmoothEmbedding_fiberProduct (G := G) (P := P) (IB := IB) (IG := IG) hn
      exact he.contMDiff_iff_comp.2 (contMDiff_fst.prodMk contMDiff_op_smul)
    contMDiff_invFun := by
      have he := isSmoothEmbedding_fiberProduct (G := G) (P := P) (IB := IB) (IG := IG) hn
      exact (contMDiff_fst.comp he.contMDiff).prodMk (contMDiff_fiberProductDivision hn)
  }

/-- The forward comparison is the action pair map. -/
@[simp]
theorem actionDiffeomorph_apply (p : T) (g : G) :
    letI := fiberProductChartedSpace (G := G) (P := P) (IB := IB) (IG := IG) hn
    (actionDiffeomorph (G := G) (P := P) (IB := IB) (IG := IG) hn (p, g)).1 = (p, op g • p) :=
  (rfl)

/-- The inverse comparison records the first point and its division element. -/
@[simp]
theorem actionDiffeomorph_symm_apply (z : R) :
    letI := fiberProductChartedSpace (G := G) (P := P) (IB := IB) (IG := IG) hn
    (actionDiffeomorph (G := G) (P := P) (IB := IB) (IG := IG) hn).symm z =
      (z.1.1, fiberProductDivision z) :=
  (rfl)

end Smooth

end TauCeti.PrincipalBundle
