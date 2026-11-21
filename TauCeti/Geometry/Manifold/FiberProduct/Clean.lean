/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Rel
public import TauCeti.Geometry.Manifold.MFDeriv.Prod
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph
public import TauCeti.Geometry.Manifold.Submersion.Descent

/-!
# Clean composites of smooth correspondences

Let `f : L₁ → M₁ × M₂` and `g : L₂ → M₂ × M₃` be smooth maps, viewed as correspondences
`M₁ ⇝ M₂` and `M₂ ⇝ M₃`. Their relational composite is the image of the fibre product
`L₁ ×_{M₂} L₂ = {(x, y) | (f x).2 = (g y).1}` under `(x, y) ↦ ((f x).1, (g y).2)`. When the
fibre product is not transverse, this map can have an *excess* kernel, and the composite is
only an immersed manifold after the excess directions are divided out.

`TauCeti.IsCleanComposite` records the data of such a clean composite: a manifold `C` with maps
`a : C → L₁` and `b : C → L₂` into the fibre product which parametrize it on tangent spaces, a
surjective submersion `q : C → Q` onto a boundaryless manifold whose vertical vectors
are exactly the excess directions, and the descended map `j : Q → M₁ × M₃`. For smooth `f` and
`g`, the descended map is smooth (`TauCeti.IsCleanComposite.contMDiff`) and an immersion
(`TauCeti.IsCleanComposite.isImmersion`). When `(a, b)` reaches every point of the fibre
product, the image of `j` is the composite of the relations `f` and `g`, that is of their images
(`TauCeti.IsCleanComposite.range_eq`).

The last statement gives **associativity** of clean composition. For three correspondences
`f`, `g` and `k`, the left grouping composes the clean composite `j₁₂` of `f` and `g` with `k`,
and the right grouping composes `f` with the clean composite `j₂₃` of `g` and `k`. When all four
clean composites exist and reach every point of their fibre products, both groupings have image
`range f ○ range g ○ range k`, by associativity of the composition of relations
(`SetRel.comp_assoc`). So when both final composites are topological embeddings, they are smooth
embeddings with the same image, and a diffeomorphism of their sources carries one to the other
(`TauCeti.IsCleanComposite.exists_diffeomorph_assoc`). Neither grouping needs its intermediate
composite to be embedded. Unlike the transverse case, the existence of one grouping does not
produce the other: the smooth excess quotients are hypotheses, not consequences.

## References

* A. Weinstein, *Symplectic categories*, Portugaliae Mathematica 67 (2010), 261–278
  (clean composition of canonical relations, and the failure of unrestricted composition).
* V. Guillemin, S. Sternberg, *Semi-classical analysis*, International Press, 2013, Chapter 4
  (clean intersections and the composition of canonical relations).
-/

public section

open Function Manifold Set Topology
open scoped Manifold ContDiff SetRel

namespace TauCeti

variable {E₁ H₁ M₁ E₂ H₂ M₂ E₃ H₃ M₃ : Type*}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁}
  [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂}
  [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
  [NormedAddCommGroup E₃] [NormedSpace ℝ E₃] [TopologicalSpace H₃] {I₃ : ModelWithCorners ℝ E₃ H₃}
  [TopologicalSpace M₃] [ChartedSpace H₃ M₃]

variable {EL₁ HL₁ L₁ EL₂ HL₂ L₂ EC HC C EQ HQ Q : Type*}
  [NormedAddCommGroup EL₁] [NormedSpace ℝ EL₁] [TopologicalSpace HL₁]
  {K₁ : ModelWithCorners ℝ EL₁ HL₁} [TopologicalSpace L₁] [ChartedSpace HL₁ L₁]
  [NormedAddCommGroup EL₂] [NormedSpace ℝ EL₂] [TopologicalSpace HL₂]
  {K₂ : ModelWithCorners ℝ EL₂ HL₂} [TopologicalSpace L₂] [ChartedSpace HL₂ L₂]
  [NormedAddCommGroup EC] [NormedSpace ℝ EC] [TopologicalSpace HC]
  {KC : ModelWithCorners ℝ EC HC} [TopologicalSpace C] [ChartedSpace HC C]
  [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
  {KQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q]
  {f : L₁ → M₁ × M₂} {g : L₂ → M₂ × M₃} {a : C → L₁} {b : C → L₂} {q : C → Q}
  {j : Q → M₁ × M₃}

variable (I₁ I₂ I₃ K₁ K₂ KC KQ) in
/-- **Clean composites of correspondences.** The map `j : Q → M₁ × M₃` is a clean composite of
the correspondences `f : L₁ → M₁ × M₂` and `g : L₂ → M₂ × M₃`, presented by the manifold `C`:

* the smooth maps `a : C → L₁` and `b : C → L₂` land in the fibre product,
  `(f (a c)).2 = (g (b c)).1`;
* `(da, db)` maps each tangent space of `C` onto the linear fibre product of the tangent spaces,
  the pairs `(u, w)` with `(df u).2 = (dg w).1`;
* `q : C → Q` is a surjective smooth submersion, and `j ∘ q` is the composite
  `c ↦ ((f (a c)).1, (g (b c)).2)`;
* the vertical vectors of `q` are exactly the excess directions, the tangent vectors `ξ` with
  `(df (da ξ)).1 = 0` and `(dg (db ξ)).2 = 0`.

A clean fibre product with a smooth quotient of its excess foliation gives these data. Cleanness
alone does not make the leaf space a manifold, so `Q` and `q` are part of the data. The image of
`j` is the whole composite of the relations `f` and `g` when `(a, b)` moreover reaches every point
of the fibre product (`TauCeti.IsCleanComposite.range_eq`). -/
structure IsCleanComposite (f : L₁ → M₁ × M₂) (g : L₂ → M₂ × M₃) (a : C → L₁) (b : C → L₂)
    (q : C → Q) (j : Q → M₁ × M₃) : Prop where
  /-- The projection of the matching manifold to `L₁` is smooth. -/
  contMDiff_left : ContMDiff KC K₁ ∞ a
  /-- The projection of the matching manifold to `L₂` is smooth. -/
  contMDiff_right : ContMDiff KC K₂ ∞ b
  /-- The matching manifold lies over the fibre product. -/
  snd_eq_fst (c : C) : (f (a c)).2 = (g (b c)).1
  /-- The matching manifold reaches every tangent pair of the linear fibre product. -/
  exists_mfderiv_eq (c : C) (u : TangentSpace K₁ (a c)) (w : TangentSpace K₂ (b c))
    (huw : (mfderiv K₁ (I₁.prod I₂) f (a c) u).2 = (mfderiv K₂ (I₂.prod I₃) g (b c) w).1) :
    ∃ ξ, mfderiv KC K₁ a c ξ = u ∧ mfderiv KC K₂ b c ξ = w
  /-- The excess quotient map is a submersion. -/
  isSubmersion : IsSubmersion KC KQ ∞ q
  /-- The excess quotient map is surjective. -/
  surjective : Surjective q
  /-- The composite factors through the excess quotient. -/
  comp_eq : j ∘ q = fun c ↦ ((f (a c)).1, (g (b c)).2)
  /-- The vertical vectors of the excess quotient are exactly the excess directions. -/
  mfderiv_eq_zero_iff (c : C) (ξ : TangentSpace KC c) : mfderiv KC KQ q c ξ = 0 ↔
    (mfderiv K₁ (I₁.prod I₂) f (a c) (mfderiv KC K₁ a c ξ)).1 = 0 ∧
      (mfderiv K₂ (I₂.prod I₃) g (b c) (mfderiv KC K₂ b c ξ)).2 = 0

namespace IsCleanComposite

/-- **The image of a clean composite is the composite of the images.** If the matching manifold
reaches every point of the fibre product, a point `(m₁, m₃)` lies in the image of `j` exactly when
`(m₁, m₂)` lies in the image of `f` and `(m₂, m₃)` in the image of `g` for some `m₂`. -/
theorem range_eq (h : IsCleanComposite I₁ I₂ I₃ K₁ K₂ KC KQ f g a b q j)
    (hab : ∀ x y, (f x).2 = (g y).1 → ∃ c, a c = x ∧ b c = y) :
    range j = range f ○ range g := by
  ext ⟨m₁, m₃⟩
  rw [SetRel.mem_comp]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨c, rfl⟩ := h.surjective y
    have hc := congrFun h.comp_eq c
    rw [comp_apply, hy] at hc
    exact ⟨(f (a c)).2, ⟨a c, Prod.ext (Prod.ext_iff.1 hc).1.symm rfl⟩,
      ⟨b c, Prod.ext (h.snd_eq_fst c).symm (Prod.ext_iff.1 hc).2.symm⟩⟩
  · rintro ⟨m₂, ⟨x, hx⟩, ⟨y, hy⟩⟩
    obtain ⟨c, rfl, rfl⟩ := hab x y (by rw [hx, hy])
    refine ⟨q c, ?_⟩
    rw [← comp_apply (f := j), h.comp_eq]
    simp only [hx, hy]

variable [KC.Boundaryless]

/-- **The clean composite is smooth.** For smooth `f` and `g`, the descended map `j` is smooth. -/
theorem contMDiff (h : IsCleanComposite I₁ I₂ I₃ K₁ K₂ KC KQ f g a b q j)
    (hf : ContMDiff K₁ (I₁.prod I₂) ∞ f) (hg : ContMDiff K₂ (I₂.prod I₃) ∞ g) :
    ContMDiff KQ (I₁.prod I₃) ∞ j := by
  refine (h.isSubmersion.contMDiff_comp_iff h.surjective le_rfl).1 ?_
  rw [h.comp_eq]
  exact (hf.fst.comp h.contMDiff_left).prodMk (hg.snd.comp h.contMDiff_right)

variable [FiniteDimensional ℝ E₁] [I₁.Boundaryless] [IsManifold I₁ ∞ M₁]
  [FiniteDimensional ℝ E₃] [I₃.Boundaryless] [IsManifold I₃ ∞ M₃]
  [KQ.Boundaryless] [IsManifold KQ ∞ Q]

/-- **The clean composite is an immersion.** For smooth `f` and `g`, the descended map `j` is an
immersion. -/
theorem isImmersion (h : IsCleanComposite I₁ I₂ I₃ K₁ K₂ KC KQ f g a b q j)
    (hf : ContMDiff K₁ (I₁.prod I₂) ∞ f) (hg : ContMDiff K₂ (I₂.prod I₃) ∞ g) :
    IsImmersion KQ (I₁.prod I₃) ∞ j := by
  refine (h.isSubmersion.isImmersion_iff_ker_mfderiv_comp h.surjective (by simp)).2
    ⟨(h.isSubmersion.contMDiff_comp_iff h.surjective le_rfl).2 (h.contMDiff hf hg), fun c ↦ ?_⟩
  ext ξ
  rw [LinearMap.mem_ker, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.coe_coe, h.comp_eq,
    (hf.mdifferentiable (by simp) (a c)).mfderiv_prodMk_fst_snd_comp_apply
      (hg.mdifferentiable (by simp) (b c)) (h.contMDiff_left.mdifferentiable (by simp) c)
      (h.contMDiff_right.mdifferentiable (by simp) c), h.mfderiv_eq_zero_iff]
  -- The zero tangent vector of the product has zero in both coordinate tangent spaces.
  exact Prod.ext_iff

section Assoc

variable {E₄ H₄ M₄ EL₃ HL₃ L₃ : Type*}
  [NormedAddCommGroup E₄] [NormedSpace ℝ E₄] [FiniteDimensional ℝ E₄] [TopologicalSpace H₄]
  {I₄ : ModelWithCorners ℝ E₄ H₄} [I₄.Boundaryless] [TopologicalSpace M₄] [ChartedSpace H₄ M₄]
  [IsManifold I₄ ∞ M₄]
  [NormedAddCommGroup EL₃] [NormedSpace ℝ EL₃] [TopologicalSpace HL₃]
  {K₃ : ModelWithCorners ℝ EL₃ HL₃} [TopologicalSpace L₃] [ChartedSpace HL₃ L₃]
  {k : L₃ → M₃ × M₄}

variable {EP₁₂ HP₁₂ P₁₂ EQ₁₂ HQ₁₂ Q₁₂ EP₂₃ HP₂₃ P₂₃ EQ₂₃ HQ₂₃ Q₂₃ : Type*}
  [NormedAddCommGroup EP₁₂] [NormedSpace ℝ EP₁₂] [TopologicalSpace HP₁₂]
  {KP₁₂ : ModelWithCorners ℝ EP₁₂ HP₁₂} [KP₁₂.Boundaryless] [TopologicalSpace P₁₂]
  [ChartedSpace HP₁₂ P₁₂]
  [NormedAddCommGroup EQ₁₂] [NormedSpace ℝ EQ₁₂] [TopologicalSpace HQ₁₂]
  {KQ₁₂ : ModelWithCorners ℝ EQ₁₂ HQ₁₂} [TopologicalSpace Q₁₂] [ChartedSpace HQ₁₂ Q₁₂]
  [NormedAddCommGroup EP₂₃] [NormedSpace ℝ EP₂₃] [TopologicalSpace HP₂₃]
  {KP₂₃ : ModelWithCorners ℝ EP₂₃ HP₂₃} [KP₂₃.Boundaryless] [TopologicalSpace P₂₃]
  [ChartedSpace HP₂₃ P₂₃]
  [NormedAddCommGroup EQ₂₃] [NormedSpace ℝ EQ₂₃] [TopologicalSpace HQ₂₃]
  {KQ₂₃ : ModelWithCorners ℝ EQ₂₃ HQ₂₃} [TopologicalSpace Q₂₃] [ChartedSpace HQ₂₃ Q₂₃]
  {a₁₂ : P₁₂ → L₁} {b₁₂ : P₁₂ → L₂} {q₁₂ : P₁₂ → Q₁₂} {j₁₂ : Q₁₂ → M₁ × M₃}
  {a₂₃ : P₂₃ → L₂} {b₂₃ : P₂₃ → L₃} {q₂₃ : P₂₃ → Q₂₃} {j₂₃ : Q₂₃ → M₂ × M₄}

variable {EPL HPL PL EQL HQL QL EPR HPR PR EQR HQR QR : Type*}
  [NormedAddCommGroup EPL] [NormedSpace ℝ EPL] [TopologicalSpace HPL]
  {KPL : ModelWithCorners ℝ EPL HPL} [KPL.Boundaryless] [TopologicalSpace PL] [ChartedSpace HPL PL]
  [NormedAddCommGroup EQL] [NormedSpace ℝ EQL] [TopologicalSpace HQL]
  {KQL : ModelWithCorners ℝ EQL HQL} [KQL.Boundaryless] [TopologicalSpace QL]
  [ChartedSpace HQL QL] [IsManifold KQL ∞ QL]
  [NormedAddCommGroup EPR] [NormedSpace ℝ EPR] [TopologicalSpace HPR]
  {KPR : ModelWithCorners ℝ EPR HPR} [KPR.Boundaryless] [TopologicalSpace PR] [ChartedSpace HPR PR]
  [NormedAddCommGroup EQR] [NormedSpace ℝ EQR] [TopologicalSpace HQR]
  {KQR : ModelWithCorners ℝ EQR HQR} [KQR.Boundaryless] [TopologicalSpace QR]
  [ChartedSpace HQR QR] [IsManifold KQR ∞ QR]
  {aL : PL → Q₁₂} {bL : PL → L₃} {qL : PL → QL} {jL : QL → M₁ × M₄}
  {aR : PR → L₁} {bR : PR → Q₂₃} {qR : PR → QR} {jR : QR → M₁ × M₄}

omit [KC.Boundaryless] [FiniteDimensional ℝ E₃] [I₃.Boundaryless] [IsManifold I₃ ∞ M₃]
  [KQ.Boundaryless] [IsManifold KQ ∞ Q] in
/-- **Associativity of clean composition.** Let `f : L₁ → M₁ × M₂`, `g : L₂ → M₂ × M₃` and
`k : L₃ → M₃ × M₄` be smooth correspondences. Suppose `j₁₂` is a clean composite of `f` and `g`,
`jL` a clean composite of `j₁₂` and `k` (the left grouping), `j₂₃` a clean composite of `g` and `k`,
and `jR` a clean composite of `f` and `j₂₃` (the right grouping), each presented by a matching
manifold reaching every point of its fibre product. If both final composites are topological
embeddings, then a diffeomorphism `e` of their sources carries one to the other, `jR ∘ e = jL`.
The intermediate composites need not be embedded. -/
theorem exists_diffeomorph_assoc (hf : ContMDiff K₁ (I₁.prod I₂) ∞ f)
    (hg : ContMDiff K₂ (I₂.prod I₃) ∞ g) (hk : ContMDiff K₃ (I₃.prod I₄) ∞ k)
    (h₁₂ : IsCleanComposite I₁ I₂ I₃ K₁ K₂ KP₁₂ KQ₁₂ f g a₁₂ b₁₂ q₁₂ j₁₂)
    (hab₁₂ : ∀ x y, (f x).2 = (g y).1 → ∃ c, a₁₂ c = x ∧ b₁₂ c = y)
    (hL : IsCleanComposite I₁ I₃ I₄ KQ₁₂ K₃ KPL KQL j₁₂ k aL bL qL jL)
    (habL : ∀ x y, (j₁₂ x).2 = (k y).1 → ∃ c, aL c = x ∧ bL c = y)
    (h₂₃ : IsCleanComposite I₂ I₃ I₄ K₂ K₃ KP₂₃ KQ₂₃ g k a₂₃ b₂₃ q₂₃ j₂₃)
    (hab₂₃ : ∀ x y, (g x).2 = (k y).1 → ∃ c, a₂₃ c = x ∧ b₂₃ c = y)
    (hR : IsCleanComposite I₁ I₂ I₄ K₁ KQ₂₃ KPR KQR f j₂₃ aR bR qR jR)
    (habR : ∀ x y, (f x).2 = (j₂₃ y).1 → ∃ c, aR c = x ∧ bR c = y)
    (hjL : IsEmbedding jL) (hjR : IsEmbedding jR) :
    ∃ e : QL ≃ₘ⟮KQL, KQR⟯ QR, ∀ y, jR (e y) = jL y := by
  have hL' : IsSmoothEmbedding KQL (I₁.prod I₄) ∞ jL :=
    ⟨hL.isImmersion (h₁₂.contMDiff hf hg) hk, hjL⟩
  have hR' : IsSmoothEmbedding KQR (I₁.prod I₄) ∞ jR :=
    ⟨hR.isImmersion hf (h₂₃.contMDiff hg hk), hjR⟩
  refine hL'.exists_diffeomorph_of_range_eq hR' ?_
  rw [hL.range_eq habL, hR.range_eq habR, h₁₂.range_eq hab₁₂, h₂₃.range_eq hab₂₃,
    SetRel.comp_assoc]

end Assoc

end IsCleanComposite

end TauCeti
