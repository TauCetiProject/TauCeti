/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
public import TauCeti.AlgebraicTopology.SimplicialObject.GeometricRealization.Basic
public import TauCeti.AlgebraicTopology.SimplicialObject.TopCat
public import TauCeti.AlgebraicTopology.TopologicalSimplex
public import TauCeti.Topology.Category.TopCat.Compact
public import TauCeti.Topology.Category.TopCat.Normal
public import TauCeti.Topology.Compactness.Paracompact

/-!
# Normal form, skeletal filtration, and point-set topology of thin geometric realization

Every point of `X.geometricRealization` decomposes uniquely into a dimension `d`, a nondegenerate
`d`-simplex of `X ⋙ forget TopCat`, and a point of `toTopInterior ⦋d⦌`
(`geometricRealization.NormalForm.realizationEquiv`). Consequently, any levelwise injective morphism
(respectively closed embedding) `φ : Y ⟶ X` induces an injective map (respectively closed embedding)
`|φ| : |Y| ⟶ |X|` with no backwards-closure hypothesis (`geometricRealization.map_injective`,
`geometricRealization.isClosedEmbedding_map`), and whenever every `X _⦋n⦌` is `T1`, `|X|` is `T1`
and compact subsets lie in the image of a single stage of `geometricRealization.skeleton X`.

When all degeneracies `X.σ j` are closed embeddings, stage `n + 1` of `skeleton X` is the pushout
of stage `n` and `X _⦋n + 1⦌ × Δⁿ⁺¹` along the closed subspace `geometricRealization.attachingSet`
(`geometricRealization.isPushout_skeleton_succ`). Hence every stage inclusion is a closed embedding,
continuous maps from compact spaces factor continuously through a single stage
(`geometricRealization.exists_lift_skeleton_of_compactSpace`), and whenever each `X _⦋n⦌ × Δⁿ` is
`T4`, `X.geometricRealization` is `T4` — hence Hausdorff, and paracompact when Lindelöf — in its
colimit topology (`geometricRealization.instT4Space`).

## References

* J. Milnor, *The geometric realization of a semi-simplicial complex*, Ann. of Math. **65** (1957).
* J. P. May, *The Geometry of Iterated Loop Spaces*, LNM **271**, Springer, 1972, §11.1–11.2.
* G. Segal, *Categories and cohomology theories*, Topology **13** (1974), 293–312, Appendix A.
-/

public noncomputable section

open CategoryTheory Limits Opposite Set Simplicial Topology

universe u

namespace CategoryTheory.SimplicialObject.geometricRealization

open SimplexCategory

variable (X : SimplicialObject TopCat.{u})

private theorem map_op_comp_apply {a b c : SimplexCategory} (f : a ⟶ b) (g : b ⟶ c)
    (x : X.obj (op c)) : X.map f.op (X.map g.op x) = X.map (f ≫ g).op x := by
  rw [op_comp, X.map_comp, TopCat.comp_app]
private theorem toTop_map_comp_apply {a b c : SimplexCategory} (f : a ⟶ b) (g : b ⟶ c)
    (u : toTop.{u}.obj a) : toTop.map g (toTop.map f u) = toTop.map (f ≫ g) u := by
  rw [toTop.map_comp, TopCat.comp_app]

section NormalForm

/-- A normal form for a point of `X.geometricRealization`: a dimension `d`, a nondegenerate
`d`-simplex of `X ⋙ forget TopCat`, and a point in the open interior of `Δᵈ`. -/
@[ext] structure NormalForm : Type u where
  /-- Dimension of the normal form. -/
  dim : ℕ
  /-- Nondegenerate simplex of the normal form. -/
  simplex : SSet.nonDegenerate (X ⋙ forget TopCat) dim
  /-- Interior coordinates in the standard topological simplex `Δᵈ`. -/
  point : toTopInterior.{u} ⦋dim⦌

/-- The point of `X.geometricRealization` represented by a normal form. -/
def NormalForm.toRealization (c : NormalForm X) : X.geometricRealization :=
  ι X c.dim (c.simplex.val, c.point.val)

/-- `NormalForm.toRealization` applies the characteristic map in the normal form's dimension. -/
theorem NormalForm.toRealization_def (c : NormalForm X) :
    c.toRealization X = ι X c.dim (c.simplex.val, c.point.val) := (rfl)

private def IsNormalForm {n : ℕ} (x : X _⦋n⦌) (t : toTop.{u}.obj ⦋n⦌) (c : NormalForm X) : Prop :=
  ∃ (k : ℕ) (μ : ⦋k⦌ ⟶ ⦋n⦌) (_ : Mono μ) (u : toTop.{u}.obj ⦋k⦌)
    (_ : u ∈ toTopInterior.{u} ⦋k⦌) (π : ⦋k⦌ ⟶ ⦋c.dim⦌) (_ : Epi π),
    toTop.map μ u = t ∧ X.map μ.op x = X.map π.op c.simplex.val ∧ toTop.map π u = c.point.val

private theorem exists_isNormalForm {n : ℕ} (x : X _⦋n⦌) (t : toTop.{u}.obj ⦋n⦌) :
    ∃ c : NormalForm X, IsNormalForm X x t c := by
  obtain ⟨k, μ, hμ, u, hu, rfl⟩ := exists_mono_toTop_map_mem_toTopInterior t
  obtain ⟨d, π, hπ, y, hy⟩ := SSet.exists_nonDegenerate (X := X ⋙ forget TopCat) (X.map μ.op x)
  exact ⟨⟨d, y, ⟨toTop.map π u, toTop_map_mem_toTopInterior_of_epi π hu⟩⟩,
    k, μ, hμ, u, hu, π, hπ, rfl, hy, rfl⟩

private theorem IsNormalForm.unique {X : SimplicialObject TopCat.{u}} {n : ℕ} {x : X _⦋n⦌}
    {t : toTop.{u}.obj ⦋n⦌} {c₁ c₂ : NormalForm X} (h₁ : IsNormalForm X x t c₁)
    (h₂ : IsNormalForm X x t c₂) : c₁ = c₂ := by
  rcases h₁ with ⟨k₁, μ₁, _, u₁, hu₁, π₁, _, ht₁, hx₁, hp₁⟩
  rcases h₂ with ⟨k₂, μ₂, _, u₂, hu₂, π₂, _, ht₂, hx₂, hp₂⟩
  cases eq_of_mono_toTop_map_mem_toTopInterior hu₁ hu₂ (ht₁.trans ht₂.symm)
  rcases c₁ with ⟨d₁, y₁, p₁⟩; rcases c₂ with ⟨d₂, y₂, p₂⟩
  dsimp only at π₁ π₂ hx₁ hx₂ hp₁ hp₂
  let S : SSet.{u} := X ⋙ forget TopCat
  obtain rfl : d₁ = d₂ := SSet.unique_nonDegenerate_dim (X := S) (X.map μ₁.op x) π₁ y₁ hx₁ π₂ y₂ hx₂
  obtain rfl : y₁ = y₂ := SSet.unique_nonDegenerate_simplex (X := S) _ π₁ y₁ hx₁ π₂ y₂ hx₂
  obtain rfl : π₁ = π₂ := SSet.unique_nonDegenerate_map (X := S) _ π₁ y₁ hx₁ π₂ y₁ hx₂
  exact congrArg (NormalForm.mk d₁ y₁) (Subtype.ext (hp₁.symm.trans hp₂))

private theorem IsNormalForm.self (c : NormalForm X) : IsNormalForm X c.simplex.val c.point.val c :=
  ⟨c.dim, 𝟙 ⦋c.dim⦌, inferInstance, c.point.val, c.point.property, 𝟙 ⦋c.dim⦌, inferInstance,
    by rw [toTop.map_id, TopCat.id_app], rfl, by rw [toTop.map_id, TopCat.id_app]⟩

private theorem IsNormalForm.of_map {X : SimplicialObject TopCat.{u}} {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    (x : X _⦋n⦌) (u₀ : toTop.{u}.obj ⦋m⦌) {c : NormalForm X}
    (hc : IsNormalForm X x (toTop.map f u₀) c) : IsNormalForm X (X.map f.op x) u₀ c := by
  obtain ⟨k, μ_u, _, u₁, hu₁, rfl⟩ := exists_mono_toTop_map_mem_toTopInterior u₀
  let p : ⦋k⦌ ⟶ ⦋(Limits.image (μ_u ≫ f)).len⦌ := Limits.factorThruImage (μ_u ≫ f)
  let μ_t : ⦋(Limits.image (μ_u ≫ f)).len⦌ ⟶ ⦋n⦌ := Limits.image.ι (μ_u ≫ f)
  have hfac : p ≫ μ_t = μ_u ≫ f := Limits.image.fac (μ_u ≫ f)
  have hu₂ := toTop_map_mem_toTopInterior_of_epi p hu₁
  have ht₂ : toTop.map μ_t (toTop.map p u₁) = toTop.map f (toTop.map μ_u u₁) := by
    rw [toTop_map_comp_apply, hfac, ← toTop_map_comp_apply]
  rcases hc with ⟨k', μ', _, u', hu', π', _, ht', hx', hp'⟩
  cases eq_of_mono_toTop_map_mem_toTopInterior hu₂ hu' (ht₂.trans ht'.symm)
  refine ⟨k, μ_u, inferInstance, u₁, hu₁, p ≫ π', epi_comp p π', rfl, ?_, ?_⟩
  · conv_lhs => rw [map_op_comp_apply X, ← hfac, ← map_op_comp_apply X, hx', map_op_comp_apply X]
  · rw [← toTop_map_comp_apply, hp']

/-- The canonical normal form associated to a point of `X.geometricRealization`. -/
def normalForm : X.geometricRealization → NormalForm X :=
  descFun (fun _ p ↦ (exists_isNormalForm X p.1 p.2).choose) fun _ _ f x t ↦
    (exists_isNormalForm X (X.map f.op x) t).choose_spec.unique
      (IsNormalForm.of_map f x t (exists_isNormalForm X x (toTop.map f t)).choose_spec)

private theorem isNormalForm_normalForm_ι {n : ℕ} (x : X _⦋n⦌) (t : toTop.{u}.obj ⦋n⦌) :
    IsNormalForm X x t (normalForm X (ι X n (x, t))) := by
  rw [normalForm, descFun_ι]; exact (exists_isNormalForm X x t).choose_spec

@[simp] theorem normalForm_toRealization (c : NormalForm X) :
    normalForm X (c.toRealization X) = c :=
  (isNormalForm_normalForm_ι X c.simplex.val c.point.val).unique (IsNormalForm.self X c)

/-- Evaluating `normalForm` on a nondegenerate simplex and an interior point recovers that normal
form. -/
@[simp] theorem normalForm_ι_of_nonDegenerate {n : ℕ} {x : X _⦋n⦌}
    (hx : x ∈ SSet.nonDegenerate (X ⋙ forget TopCat) n) {t : toTop.{u}.obj ⦋n⦌}
    (ht : t ∈ toTopInterior.{u} ⦋n⦌) : normalForm X (ι X n (x, t)) = ⟨n, ⟨x, hx⟩, ⟨t, ht⟩⟩ :=
  normalForm_toRealization X ⟨n, ⟨x, hx⟩, ⟨t, ht⟩⟩

@[simp] theorem toRealization_normalForm (p : X.geometricRealization) :
    (normalForm X p).toRealization X = p := by
  obtain ⟨n, x, t, rfl⟩ := ι_jointly_surjective X p
  rcases isNormalForm_normalForm_ι X x t with ⟨k, μ, _, u, _, π, _, ht, hx, hp⟩
  rw [NormalForm.toRealization, ← hp, ← ι_map, ← hx, ι_map, ht]

/-- **Canonical normal-form decomposition of thin geometric realization.** Every point of `|X|` is
represented by a unique nondegenerate simplex together with a point in the open simplex interior. -/
@[expose, simps] def NormalForm.realizationEquiv : NormalForm X ≃ X.geometricRealization :=
  ⟨NormalForm.toRealization X, normalForm X, normalForm_toRealization X, toRealization_normalForm X⟩

end NormalForm

section MapEmbedding

variable {X} {Y : SimplicialObject TopCat.{u}} {φ : Y ⟶ X}

private abbrev mapNormalForm (hinj : ∀ n : ℕ, Function.Injective (φ.app (op ⦋n⦌)))
    (c : NormalForm Y) : NormalForm X :=
  have : ∀ Δ : SimplexCategoryᵒᵖ, Mono ((Functor.whiskerRight φ (forget TopCat)).app Δ) :=
    fun ⟨⟨n⟩⟩ ↦ (CategoryTheory.mono_iff_injective _).mpr (hinj n)
  have : Mono (Functor.whiskerRight φ (forget TopCat)) := NatTrans.mono_of_mono_app _
  ⟨c.dim, ⟨φ.app (op ⦋c.dim⦌) c.simplex.val,
    (SSet.nonDegenerate_iff_of_mono (Functor.whiskerRight φ (forget TopCat)) _).mpr
      c.simplex.property⟩,
    c.point⟩

private theorem normalForm_map (hinj : ∀ n : ℕ, Function.Injective (φ.app (op ⦋n⦌)))
    (q : Y.geometricRealization) :
    normalForm X (map φ q) = mapNormalForm hinj (normalForm Y q) := by
  conv_lhs => rw [← toRealization_normalForm Y q]
  exact (map_ι φ _ _ _) ▸ normalForm_toRealization X (mapNormalForm hinj (normalForm Y q))

/-- **Injectivity for thin geometric realization.** Any levelwise injective morphism `φ : Y ⟶ X`
of simplicial spaces induces an injective map `|φ| : |Y| ⟶ |X|`, with no backwards-closure
hypothesis. -/
theorem map_injective (hinj : ∀ n : ℕ, Function.Injective (φ.app (op ⦋n⦌))) :
    Function.Injective (map φ) := fun q₁ q₂ h ↦ by
  have hc := (normalForm_map hinj q₁).symm.trans ((congrArg (normalForm X) h).trans
    (normalForm_map hinj q₂))
  rcases h₁ : normalForm Y q₁ with ⟨d₁, y₁, p₁⟩; rcases h₂ : normalForm Y q₂ with ⟨d₂, y₂, p₂⟩
  rw [h₁, h₂] at hc; obtain rfl : d₁ = d₂ := congrArg NormalForm.dim hc
  injection hc with _ hsimp hp
  have hy : y₁ = y₂ := Subtype.ext (hinj d₁ (congrArg Subtype.val hsimp))
  exact (toRealization_normalForm Y q₁).symm.trans <|
    (congrArg (NormalForm.toRealization Y) (by rw [h₁, h₂, hy]; exact congrArg _ hp)).trans
      (toRealization_normalForm Y q₂)

private theorem preimage_ι_image_map_eq_iUnion
    (hinj : ∀ n : ℕ, Function.Injective (φ.app (op ⦋n⦌)))
    (W : Set Y.geometricRealization) (n : ℕ) :
    ι X n ⁻¹' (map φ '' W) =
      ⋃ (m : Fin (n + 1)) (μ : ⦋m.val⦌ ⟶ ⦋n⦌) (_ : Mono μ),
        Prod.map id (toTop.map μ) '' (Prod.map (X.map μ.op) id ⁻¹'
          (Prod.map (φ.app (op ⦋m.val⦌)) id '' (ι Y m.val ⁻¹' W))) := by
  ext ⟨x, t⟩; simp only [mem_iUnion, mem_preimage, mem_image]; constructor
  · rintro ⟨q, hq, hqx⟩
    have hnf : normalForm X (ι X n (x, t)) = mapNormalForm hinj (normalForm Y q) :=
      hqx ▸ normalForm_map hinj q
    rcases hnf ▸ isNormalForm_normalForm_ι X x t with ⟨k, μ, hμ, u, _, π, _, ht, hx, hp⟩
    let y : Y _⦋k⦌ := Y.map π.op (normalForm Y q).simplex.val
    have hiy : ι Y k (y, u) = q := (ι_map Y π _ u).trans (hp.symm ▸ toRealization_normalForm Y q)
    exact ⟨⟨k, Nat.lt_succ_of_le (le_of_mono μ)⟩, μ, hμ, (x, u),
      ⟨(y, u), (congrArg (· ∈ W) hiy).mpr hq,
        Prod.ext ((NatTrans.naturality_apply φ π.op _).trans hx.symm) rfl⟩, Prod.ext rfl ht⟩
  · rintro ⟨m, μ, _, ⟨_, _⟩, ⟨⟨y, u⟩, hyW, hxy⟩, hxt⟩
    simp only [Prod.map_apply, id_eq, Prod.mk.injEq] at hxy hxt
    obtain ⟨hφy, rfl⟩ := hxy; obtain ⟨rfl, rfl⟩ := hxt
    exact ⟨ι Y m.val (y, u), hyW, by rw [map_ι, hφy, ι_map]⟩

/-- **Closed restriction for thin geometric realization.** Any levelwise closed embedding
`φ : Y ⟶ X` of simplicial spaces induces a closed embedding `|φ| : |Y| ⟶ |X|`, with no
backwards-closure hypothesis. -/
theorem isClosedEmbedding_map (hφ : ∀ n : ℕ, IsClosedEmbedding (φ.app (op ⦋n⦌))) :
    IsClosedEmbedding (map φ) := by
  have hinj : ∀ n : ℕ, Function.Injective (φ.app (op ⦋n⦌)) := fun n ↦ (hφ n).injective
  refine .of_continuous_injective_isClosedMap (map φ).hom.continuous (map_injective hinj)
    fun W hW ↦ (isClosed_iff X).mpr fun n ↦ ?_
  rw [preimage_ι_image_map_eq_iUnion hinj W n]
  refine isClosed_iUnion_of_finite fun m ↦ isClosed_iUnion_of_finite fun μ ↦
    isClosed_iUnion_of_finite fun _ ↦ ?_
  exact (IsClosedEmbedding.id.prodMap (isClosedEmbedding_toTop_map_of_mono μ)).isClosedMap _ <|
    (((hφ m.val).prodMap .id).isClosedMap _ ((isClosed_iff Y).mp hW m.val)).preimage
      (((X.map μ.op).hom.continuous.comp continuous_fst).prodMk continuous_snd)

end MapEmbedding

section Skeleton

private inductive SkeletonRel (n : ℕ) :
    (Σ k : {k : ℕ // k ≤ n}, X _⦋k.val⦌ × toTop.{u}.obj ⦋k.val⦌) →
      (Σ k : {k : ℕ // k ≤ n}, X _⦋k.val⦌ × toTop.{u}.obj ⦋k.val⦌) → Prop where
  | mk {l k : ℕ} (hl : l ≤ n) (hk : k ≤ n) (f : ⦋l⦌ ⟶ ⦋k⦌) (x : X _⦋k⦌) (t : toTop.{u}.obj ⦋l⦌) :
      SkeletonRel n ⟨⟨l, hl⟩, X.map f.op x, t⟩ ⟨⟨k, hk⟩, x, toTop.map f t⟩

/-- The skeletal filtration `n ↦ skₙ |X|` of `X.geometricRealization`: stage `n` is the quotient
of `Σ k ≤ n, X _⦋k⦌ × Δᵏ` by the simplicial identifications in degrees at most `n`. -/
def skeleton : ℕ ⥤ TopCat.{u} where
  obj n := TopCat.of (Quot (SkeletonRel X n))
  map {m n} f := TopCat.ofHom
    { toFun := Quot.lift
        (fun p ↦ Quot.mk (SkeletonRel X n) ⟨⟨p.1.val, p.1.property.trans (leOfHom f)⟩, p.2⟩)
        (by rintro _ _ ⟨hl, hk, g, x, t⟩
            exact Quot.sound (SkeletonRel.mk (hl.trans (leOfHom f)) (hk.trans (leOfHom f)) g x t))
      continuous_toFun := continuous_quot_lift _ (continuous_sigma fun k ↦
        continuous_quot_mk.comp (continuous_sigmaMk
          (σ := fun j : {j : ℕ // j ≤ n} ↦ X _⦋j.val⦌ × toTop.{u}.obj ⦋j.val⦌)
          (i := ⟨k.val, k.property.trans (leOfHom f)⟩))) }
  map_id _ := by ext q; induction q using Quot.ind with | mk _ => rfl
  map_comp _ _ := by ext q; induction q using Quot.ind with | mk _ => rfl

/-- Characteristic map `X _⦋k⦌ × Δᵏ → skₙ |X|` for `k ≤ n`. -/
def skeleton.ι (n : ℕ) {k : ℕ} (hk : k ≤ n) : C(X _⦋k⦌ × toTop.{u}.obj ⦋k⦌, (skeleton X).obj n) :=
  ⟨fun p ↦ Quot.mk (SkeletonRel X n) ⟨⟨k, hk⟩, p⟩, continuous_quot_mk.comp continuous_sigmaMk⟩

@[simp] theorem skeleton.ι_map (n : ℕ) {l k : ℕ} (hl : l ≤ n) (hk : k ≤ n) (f : ⦋l⦌ ⟶ ⦋k⦌)
    (x : X _⦋k⦌) (t : toTop.{u}.obj ⦋l⦌) :
    skeleton.ι X n hl (X.map f.op x, t) = skeleton.ι X n hk (x, toTop.map f t) :=
  Quot.sound (SkeletonRel.mk hl hk f x t)

theorem skeleton.ι_jointly_surjective {n : ℕ} (q : (skeleton X).obj n) :
    ∃ (k : ℕ) (hk : k ≤ n) (x : X _⦋k⦌) (t : toTop.{u}.obj ⦋k⦌),
      skeleton.ι X n hk (x, t) = q := by
  induction q using Quot.ind with | mk p => exact ⟨p.1.val, p.1.property, p.2.1, p.2.2, rfl⟩

/-- The `n`-skeleton carries the quotient topology from `Σ k : {k // k ≤ n}, X _⦋k⦌ × Δᵏ`. -/
theorem skeleton.isQuotientMap_sigma (n : ℕ) :
    IsQuotientMap fun p : Σ k : {k : ℕ // k ≤ n}, X _⦋k.val⦌ × toTop.{u}.obj ⦋k.val⦌ ↦
      skeleton.ι X n p.1.property p.2 := isQuotientMap_quot_mk

theorem skeleton.isOpen_iff {n : ℕ} {s : Set ((skeleton X).obj n)} :
    IsOpen s ↔ ∀ (k : ℕ) (hk : k ≤ n), IsOpen (skeleton.ι X n hk ⁻¹' s) := by
  rw [← (skeleton.isQuotientMap_sigma X n).isOpen_preimage, isOpen_sigma_iff, Subtype.forall]; rfl

theorem skeleton.isClosed_iff {n : ℕ} {s : Set ((skeleton X).obj n)} :
    IsClosed s ↔ ∀ (k : ℕ) (hk : k ≤ n), IsClosed (skeleton.ι X n hk ⁻¹' s) := by
  simp only [← isOpen_compl_iff, skeleton.isOpen_iff, preimage_compl]

theorem skeleton.continuous_iff {n : ℕ} {Z : Type*} [TopologicalSpace Z]
    {g : (skeleton X).obj n → Z} :
    Continuous g ↔ ∀ (k : ℕ) (hk : k ≤ n), Continuous (g ∘ skeleton.ι X n hk) := by
  rw [(skeleton.isQuotientMap_sigma X n).continuous_iff, continuous_sigma_iff, Subtype.forall]; rfl

@[ext] theorem skeleton.hom_ext {n : ℕ} {Z : TopCat.{u}} {g h : (skeleton X).obj n ⟶ Z}
    (H : ∀ (k : ℕ) (hk : k ≤ n) (x : X _⦋k⦌) (t : toTop.{u}.obj ⦋k⦌),
      g (skeleton.ι X n hk (x, t)) = h (skeleton.ι X n hk (x, t))) : g = h := by
  ext q; obtain ⟨k, hk, x, t, rfl⟩ := skeleton.ι_jointly_surjective X q; exact H k hk x t

section Desc

variable (n : ℕ) {Z : Type*} [TopologicalSpace Z]
  (g : ∀ (k : ℕ), k ≤ n → C(X _⦋k⦌ × toTop.{u}.obj ⦋k⦌, Z))
  (hg : ∀ ⦃l k : ℕ⦄ (hl : l ≤ n) (hk : k ≤ n) (f : ⦋l⦌ ⟶ ⦋k⦌) (x : X _⦋k⦌)
    (t : toTop.{u}.obj ⦋l⦌), g l hl (X.map f.op x, t) = g k hk (x, toTop.map f t))

/-- Universal property of the `n`-skeleton: continuous maps `X _⦋k⦌ × Δᵏ → Z` (`k ≤ n`) compatible
with all simplicial operators in degrees at most `n` descend to a continuous map `skₙ |X| → Z`. -/
def skeleton.desc : C((skeleton X).obj n, Z) where
  toFun := Quot.lift (fun p ↦ g p.1.val p.1.property p.2)
    (by rintro _ _ ⟨hl, hk, f, x, t⟩; exact hg hl hk f x t)
  continuous_toFun :=
    continuous_quot_lift _ (continuous_sigma fun k ↦ (g k.val k.property).continuous)

@[simp] theorem skeleton.desc_ι {k : ℕ} (hk : k ≤ n) (p : X _⦋k⦌ × toTop.{u}.obj ⦋k⦌) :
    skeleton.desc X n g hg (skeleton.ι X n hk p) = g k hk p := (rfl)

end Desc

@[simp] theorem skeleton.map_ι {m n k : ℕ} (f : m ⟶ n) (hk : k ≤ m)
    (p : X _⦋k⦌ × toTop.{u}.obj ⦋k⦌) :
    (skeleton X).map f (skeleton.ι X m hk p) = skeleton.ι X n (hk.trans (leOfHom f)) p := (rfl)

/-- Characteristic morphism `TopCat.of (X _⦋k⦌ × Δᵏ) ⟶ skₙ |X|` in `TopCat` for `k ≤ n`. -/
def skeleton.ιHom (n : ℕ) {k : ℕ} (hk : k ≤ n) :
    TopCat.of (X _⦋k⦌ × toTop.{u}.obj ⦋k⦌) ⟶ (skeleton X).obj n :=
  ConcreteCategory.ofHom (skeleton.ι X n hk)

@[simp] theorem skeleton.ιHom_apply (n : ℕ) {k : ℕ} (hk : k ≤ n) (p : X _⦋k⦌ × toTop.{u}.obj ⦋k⦌) :
    skeleton.ιHom X n hk p = skeleton.ι X n hk p := (rfl)

/-- Stage inclusion morphism `skₙ |X| ⟶ |X|` in `TopCat`. -/
def skeleton.toRealization (n : ℕ) : (skeleton X).obj n ⟶ X.geometricRealization :=
  TopCat.ofHom <| skeleton.desc X n (fun k _ ↦ geometricRealization.ι X k)
    fun _ _ _ _ f x t ↦ geometricRealization.ι_map X f x t

@[simp] theorem skeleton.toRealization_ι (n : ℕ) {k : ℕ} (hk : k ≤ n)
    (p : X _⦋k⦌ × toTop.{u}.obj ⦋k⦌) :
    skeleton.toRealization X n (skeleton.ι X n hk p) = geometricRealization.ι X k p := (rfl)

@[reassoc (attr := simp)] theorem skeleton_map_comp_toRealization {m n : ℕ} (f : m ⟶ n) :
    (skeleton X).map f ≫ skeleton.toRealization X n = skeleton.toRealization X m := by
  ext k hk x t; simp

instance (n : ℕ) [∀ k : {k : ℕ // k ≤ n}, LindelofSpace (X _⦋k.val⦌ × toTop.{u}.obj ⦋k.val⦌)] :
    LindelofSpace ((skeleton X).obj n) := Quot.lindelofSpace

/-- The canonical cocone exhibiting `X.geometricRealization` above `skeleton X`. -/
@[expose, simps] def skeletonCocone : Cocone (skeleton X) where
  pt := X.geometricRealization
  ι := { app := skeleton.toRealization X
         naturality _ _ f := (skeleton_map_comp_toRealization X f).trans (Category.comp_id _).symm }

private def skeletonCoconeDesc (s : Cocone (skeleton X)) : X.geometricRealization ⟶ s.pt :=
  ConcreteCategory.ofHom (C := TopCat) <|
    desc (Z := s.pt) (fun n ↦ (s.ι.app n).hom.comp (skeleton.ι X n le_rfl))
      fun m n f x t ↦ by
        have hm := ConcreteCategory.congr_hom (s.w (homOfLE (le_max_left m n)))
          (skeleton.ι X m le_rfl (X.map f.op x, t))
        have hn := ConcreteCategory.congr_hom (s.w (homOfLE (le_max_right m n)))
          (skeleton.ι X n le_rfl (x, toTop.map f t))
        simp only [TopCat.coe_comp, Function.comp_apply, skeleton.map_ι] at hm hn
        simp only [ContinuousMap.coe_comp, Function.comp_apply, ← hm, ← hn,
          skeleton.ι_map X (max m n) (le_max_left m n) (le_max_right m n) f x t]

@[simp] private theorem skeletonCoconeDesc_ι (s : Cocone (skeleton X)) (n : ℕ)
    (p : X _⦋n⦌ × toTop.{u}.obj ⦋n⦌) :
    skeletonCoconeDesc X s (ι X n p) = s.ι.app n (skeleton.ι X n le_rfl p) := by
  simp [skeletonCoconeDesc]

/-- `X.geometricRealization` is the colimit in `TopCat` of its skeletal filtration `skeleton X`. -/
def isColimitSkeletonCocone : IsColimit (skeletonCocone X) where
  desc s := skeletonCoconeDesc X s
  fac s n := by
    dsimp only [skeletonCocone]; ext k hk x t
    have hw := ConcreteCategory.congr_hom (s.w (homOfLE hk)) (skeleton.ι X k le_rfl (x, t))
    simp only [TopCat.comp_app, skeleton.map_ι] at hw
    rw [TopCat.comp_app, skeleton.toRealization_ι, skeletonCoconeDesc_ι, hw]
  uniq s m hm := by
    dsimp only [skeletonCocone] at m hm ⊢; refine hom_ext X fun n x t ↦ ?_
    have hmn := ConcreteCategory.congr_hom (hm n) (skeleton.ι X n le_rfl (x, t))
    rw [TopCat.comp_app, skeleton.toRealization_ι] at hmn
    simpa only [skeletonCoconeDesc_ι] using hmn

private theorem skeleton_ι_eq_normalForm {n k : ℕ} (hk : k ≤ n) (x : X _⦋k⦌)
    (t : toTop.{u}.obj ⦋k⦌) {c : NormalForm X} (hc : IsNormalForm X x t c) :
    ∃ hd : c.dim ≤ n,
      skeleton.ι X n hk (x, t) = skeleton.ι X n hd (c.simplex.val, c.point.val) := by
  rcases hc with ⟨r, μ, _, u, _, π, _, ht, hx, hp⟩
  have hr : r ≤ n := (le_of_mono μ).trans hk
  refine ⟨(le_of_epi π).trans hr, ?_⟩
  rw [← ht, ← skeleton.ι_map X n hr hk μ, hx, skeleton.ι_map X n hr _ π, hp]

/-- Every stage inclusion `skₙ |X| ⟶ |X|` is unconditionally injective. -/
theorem skeleton.toRealization_injective (n : ℕ) :
    Function.Injective (skeleton.toRealization X n) := fun q₁ q₂ h ↦ by
  obtain ⟨k₁, hk₁, x₁, t₁, rfl⟩ := skeleton.ι_jointly_surjective X q₁
  obtain ⟨k₂, hk₂, x₂, t₂, rfl⟩ := skeleton.ι_jointly_surjective X q₂
  have hreal : geometricRealization.ι X k₁ (x₁, t₁) = geometricRealization.ι X k₂ (x₂, t₂) := by
    simpa only [skeleton.toRealization_ι] using h
  obtain ⟨_, heq₁⟩ := skeleton_ι_eq_normalForm X hk₁ x₁ t₁ (isNormalForm_normalForm_ι X x₁ t₁)
  obtain ⟨_, heq₂⟩ := skeleton_ι_eq_normalForm X hk₂ x₂ t₂
    (hreal ▸ isNormalForm_normalForm_ι X x₂ t₂)
  exact heq₁.trans heq₂.symm

/-- Every skeletal transition map `skₘ |X| ⟶ skₙ |X|` (`m ≤ n`) is unconditionally injective. -/
theorem skeleton_map_injective {m n : ℕ} (hmn : m ≤ n) :
    Function.Injective ((skeleton X).map (homOfLE hmn)) :=
  .of_comp (f := skeleton.toRealization X n) <| by
    rw [← TopCat.coe_comp, skeleton_map_comp_toRealization]
    exact skeleton.toRealization_injective X m

/-- The `0`-skeleton of `X.geometricRealization` is isomorphic in `TopCat` to `X _⦋0⦌`. -/
def skeletonZeroIso : (skeleton X).obj 0 ≅ X _⦋0⦌ where
  hom := ConcreteCategory.ofHom (C := TopCat) <| skeleton.desc X 0
    (fun k _ ↦ (X.map (SimplexCategory.const ⦋0⦌ ⦋k⦌ 0).op).hom.comp ContinuousMap.fst)
    fun _ _ hl hk f _ _ ↦ by
      obtain rfl := Nat.eq_zero_of_le_zero hl; obtain rfl := Nat.eq_zero_of_le_zero hk
      obtain rfl : f = 𝟙 ⦋0⦌ := Subsingleton.elim f (𝟙 ⦋0⦌); simp
  inv := ConcreteCategory.ofHom (C := TopCat) <| (skeleton.ι X 0 le_rfl).comp
    ⟨fun x ↦ (x, default), continuous_id.prodMk continuous_const⟩
  hom_inv_id := by
    ext k hk x t; obtain rfl := Nat.eq_zero_of_le_zero hk
    obtain rfl : t = default := Subsingleton.elim t default; simp
  inv_hom_id := TopCat.ext fun x ↦ by simp

@[simp] theorem skeletonZeroIso_hom_ι (x : X _⦋0⦌) (t : toTop.{u}.obj ⦋0⦌) :
    (skeletonZeroIso X).hom (skeleton.ι X 0 le_rfl (x, t)) = x := by simp [skeletonZeroIso]

@[simp] theorem skeletonZeroIso_inv_apply (x : X _⦋0⦌) :
    (skeletonZeroIso X).inv x = skeleton.ι X 0 le_rfl (x, default) := (rfl)

@[reassoc] theorem skeletonZeroIso_inv_comp_toRealization :
    (skeletonZeroIso X).inv ≫ skeleton.toRealization X 0 =
      ConcreteCategory.ofHom (C := TopCat)
        ((ι X 0).comp ⟨fun x ↦ (x, default), continuous_id.prodMk continuous_const⟩) :=
  TopCat.ext fun x ↦ by simp

end Skeleton

section Pushout

/-- The attaching locus inside `X _⦋n⦌ × Δⁿ`: points whose simplex is degenerate or whose
barycentric coordinates lie in the topological boundary `∂Δⁿ`. -/
def attachingSet (n : ℕ) : Set (X _⦋n⦌ × toTop.{u}.obj ⦋n⦌) :=
  SSet.degenerate (X ⋙ forget TopCat) n ×ˢ univ ∪ univ ×ˢ toTopBoundary.{u} ⦋n⦌

theorem attachingSet_def (n : ℕ) :
    attachingSet X n =
      SSet.degenerate (X ⋙ forget TopCat) n ×ˢ univ ∪ univ ×ˢ toTopBoundary.{u} ⦋n⦌ := (rfl)

@[simp] theorem mem_attachingSet_iff {n : ℕ} {p : X _⦋n⦌ × toTop.{u}.obj ⦋n⦌} :
    p ∈ attachingSet X n ↔
      p.1 ∈ SSet.degenerate (X ⋙ forget TopCat) n ∨ p.2 ∈ toTopBoundary.{u} ⦋n⦌ := by
  simp [attachingSet]

/-- If the degenerate `n`-simplices form a closed subset of `X _⦋n⦌`, the attaching locus is closed
in `X _⦋n⦌ × Δⁿ`. -/
theorem isClosed_attachingSet {n : ℕ}
    (hdeg : IsClosed (X := X _⦋n⦌) (SSet.degenerate (X ⋙ forget TopCat) n)) :
    IsClosed (attachingSet X n) :=
  (hdeg.prod isClosed_univ).union (isClosed_univ.prod (isClosed_toTopBoundary ⦋n⦌))

private theorem mem_range_succ_of_mem_attachingSet {n : ℕ}
    {p : X _⦋n + 1⦌ × toTop.{u}.obj ⦋n + 1⦌} (hp : p ∈ attachingSet X (n + 1)) :
    skeleton.ι X (n + 1) le_rfl p ∈ range ((skeleton X).map (homOfLE n.le_succ)) := by
  rcases p with ⟨x, t⟩; rcases hp with ⟨hx, -⟩ | ⟨-, ht⟩
  · obtain ⟨j, y, rfl⟩ := mem_iUnion.mp (SSet.degenerate_eq_iUnion_range_σ (X ⋙ forget TopCat) ▸ hx)
    exact ⟨skeleton.ι X n le_rfl (y, toTop.map (SimplexCategory.σ j) t),
      (skeleton.map_ι X (homOfLE n.le_succ) le_rfl _).trans
        (skeleton.ι_map X (n + 1) le_rfl n.le_succ (SimplexCategory.σ j) y t).symm⟩
  · obtain ⟨i, u, rfl⟩ := mem_iUnion.mp (toTopBoundary_eq_iUnion_range_δ n ▸ ht)
    exact ⟨skeleton.ι X n le_rfl (X.δ i x, u),
      (skeleton.map_ι X (homOfLE n.le_succ) le_rfl _).trans
        (skeleton.ι_map X (n + 1) n.le_succ le_rfl (SimplexCategory.δ i) x u)⟩

private def attachingFun (n : ℕ) (a : attachingSet X (n + 1)) : (skeleton X).obj n :=
  (mem_range_succ_of_mem_attachingSet X a.property).choose

private theorem attachingFun_spec {n : ℕ} (a : attachingSet X (n + 1)) :
    (skeleton X).map (homOfLE n.le_succ) (attachingFun X n a) = skeleton.ι X (n + 1) le_rfl a.val :=
  (mem_range_succ_of_mem_attachingSet X a.property).choose_spec

private theorem attachingFun_map_left {n k : ℕ} (hk : k ≤ n) (f : ⦋n + 1⦌ ⟶ ⦋k⦌) (y : X _⦋k⦌)
    (t : toTop.{u}.obj ⦋n + 1⦌) (h : (X.map f.op y, t) ∈ attachingSet X (n + 1)) :
    attachingFun X n ⟨(X.map f.op y, t), h⟩ = skeleton.ι X n hk (y, toTop.map f t) :=
  skeleton_map_injective X n.le_succ <| (attachingFun_spec X _).trans <|
    (skeleton.ι_map X (n + 1) le_rfl (hk.trans n.le_succ) f y t).trans
      (skeleton.map_ι X (homOfLE n.le_succ) hk _).symm

private theorem attachingFun_map_right {n l : ℕ} (hl : l ≤ n) (f : ⦋l⦌ ⟶ ⦋n + 1⦌) (x : X _⦋n + 1⦌)
    (u : toTop.{u}.obj ⦋l⦌) (h : (x, toTop.map f u) ∈ attachingSet X (n + 1)) :
    attachingFun X n ⟨(x, toTop.map f u), h⟩ = skeleton.ι X n hl (X.map f.op x, u) :=
  skeleton_map_injective X n.le_succ <| (attachingFun_spec X _).trans <|
    (skeleton.ι_map X (n + 1) (hl.trans n.le_succ) le_rfl f x u).symm.trans
      (skeleton.map_ι X (homOfLE n.le_succ) hl _).symm

private theorem image_val_preimage_attachingFun {n : ℕ} (F : Set ((skeleton X).obj n)) :
    Subtype.val '' (attachingFun X n ⁻¹' F) =
      (⋃ j : Fin (n + 1), Prod.map (X.σ j) id ''
        ((fun p ↦ skeleton.ι X n le_rfl (p.1, toTop.map (SimplexCategory.σ j) p.2)) ⁻¹' F)) ∪
      (⋃ i : Fin (n + 2), Prod.map id (toTop.map (SimplexCategory.δ i)) ''
        ((fun p ↦ skeleton.ι X n le_rfl (X.δ i p.1, p.2)) ⁻¹' F)) := by
  ext p; constructor
  · rintro ⟨⟨⟨x, t⟩, hmem⟩, hF, rfl⟩
    have hmem' := hmem; rcases hmem' with ⟨hx, -⟩ | ⟨-, ht⟩
    · obtain ⟨j, y, rfl⟩ :=
        mem_iUnion.mp (SSet.degenerate_eq_iUnion_range_σ (X ⋙ forget TopCat) ▸ hx)
      exact Or.inl <| mem_iUnion.mpr ⟨j, (y, t), (congrArg (· ∈ F)
        (attachingFun_map_left X le_rfl (SimplexCategory.σ j) y t hmem)).mp hF, rfl⟩
    · obtain ⟨i, u, rfl⟩ := mem_iUnion.mp (toTopBoundary_eq_iUnion_range_δ n ▸ ht)
      exact Or.inr <| mem_iUnion.mpr ⟨i, (x, u), (congrArg (· ∈ F)
        (attachingFun_map_right X le_rfl (SimplexCategory.δ i) x u hmem)).mp hF, rfl⟩
  · rintro (hσ | hδ)
    · obtain ⟨j, ⟨y, t⟩, hy, rfl⟩ := mem_iUnion.mp hσ
      have hmem : (X.σ j y, t) ∈ attachingSet X (n + 1) :=
        Or.inl ⟨SSet.σ_mem_degenerate (X := X ⋙ forget TopCat) j y, trivial⟩
      exact ⟨⟨(X.σ j y, t), hmem⟩, (congrArg (· ∈ F)
        (attachingFun_map_left X le_rfl (SimplexCategory.σ j) y t hmem)).mpr hy, rfl⟩
    · obtain ⟨i, ⟨x, u⟩, hx, rfl⟩ := mem_iUnion.mp hδ
      have hmem : (x, toTop.map (SimplexCategory.δ i) u) ∈ attachingSet X (n + 1) :=
        Or.inr ⟨trivial, toTop_map_mem_toTopBoundary_of_len_lt (SimplexCategory.δ i) (by simp) u⟩
      exact ⟨⟨(x, toTop.map (SimplexCategory.δ i) u), hmem⟩, (congrArg (· ∈ F)
        (attachingFun_map_right X le_rfl (SimplexCategory.δ i) x u hmem)).mpr hx, rfl⟩

private theorem continuous_attachingFun {n : ℕ}
    (hσ : ∀ j : Fin (n + 1), IsClosedEmbedding (X.σ j)) : Continuous (attachingFun X n) := by
  rw [continuous_iff_isClosed]; intro F hF
  rw [← preimage_image_eq (attachingFun X n ⁻¹' F) Subtype.val_injective]
  refine IsClosed.preimage continuous_subtypeVal ?_; rw [image_val_preimage_attachingFun]
  refine (isClosed_iUnion_of_finite fun j ↦ ?_).union (isClosed_iUnion_of_finite fun i ↦ ?_)
  · exact ((hσ j).prodMap .id).isClosedMap _ (hF.preimage <| (skeleton.ι X n le_rfl).continuous.comp
      (continuous_fst.prodMk ((toTop.map (SimplexCategory.σ j)).hom.continuous.comp
        continuous_snd)))
  · exact (IsClosedEmbedding.id.prodMap (isClosedEmbedding_toTop_map_of_mono
      (SimplexCategory.δ i))).isClosedMap _ (hF.preimage <| (skeleton.ι X n le_rfl).continuous.comp
      (((X.δ i).hom.continuous.comp continuous_fst).prodMk continuous_snd))

/-- The continuous attaching map `attachingSet X (n + 1) ⟶ skₙ |X|` when all degeneracies in
degree `n` are closed embeddings. -/
def attachingMap (n : ℕ) (hσ : ∀ j : Fin (n + 1), IsClosedEmbedding (X.σ j)) :
    TopCat.of (attachingSet X (n + 1)) ⟶ (skeleton X).obj n :=
  TopCat.ofHom ⟨attachingFun X n, continuous_attachingFun X hσ⟩

@[simp] theorem skeleton_map_attachingMap_apply {n : ℕ}
    (hσ : ∀ j : Fin (n + 1), IsClosedEmbedding (X.σ j)) (a : attachingSet X (n + 1)) :
    (skeleton X).map (homOfLE n.le_succ) (attachingMap X n hσ a) =
      skeleton.ι X (n + 1) le_rfl a.val := attachingFun_spec X a

@[reassoc (attr := simp)]
theorem attachingMap_comp_skeleton_map (n : ℕ) (hσ : ∀ j : Fin (n + 1), IsClosedEmbedding (X.σ j)) :
    attachingMap X n hσ ≫ (skeleton X).map (homOfLE n.le_succ) =
      TopCat.ofHom ⟨Subtype.val, continuous_subtypeVal⟩ ≫ skeleton.ιHom X (n + 1) le_rfl := by
  ext a; exact attachingFun_spec X a

/-- Evaluating `attachingMap` on a simplex factored through degree `k ≤ n`. -/
@[simp] theorem attachingMap_map_left {n k : ℕ} (hσ : ∀ j : Fin (n + 1), IsClosedEmbedding (X.σ j))
    (hk : k ≤ n) (f : ⦋n + 1⦌ ⟶ ⦋k⦌) (y : X _⦋k⦌) (t : toTop.{u}.obj ⦋n + 1⦌)
    (h : (X.map f.op y, t) ∈ attachingSet X (n + 1)) :
    attachingMap X n hσ ⟨(X.map f.op y, t), h⟩ = skeleton.ι X n hk (y, toTop.map f t) :=
  attachingFun_map_left X hk f y t h

/-- Evaluating `attachingMap` on coordinates in the image of a morphism from degree `l ≤ n`. -/
@[simp↓] theorem attachingMap_map_right {n l : ℕ}
    (hσ : ∀ j : Fin (n + 1), IsClosedEmbedding (X.σ j)) (hl : l ≤ n) (f : ⦋l⦌ ⟶ ⦋n + 1⦌)
    (x : X _⦋n + 1⦌) (u : toTop.{u}.obj ⦋l⦌) (h : (x, toTop.map f u) ∈ attachingSet X (n + 1)) :
    attachingMap X n hσ ⟨(x, toTop.map f u), h⟩ = skeleton.ι X n hl (X.map f.op x, u) :=
  attachingFun_map_right X hl f x u h

section PushoutDesc

variable {n : ℕ} {Z : TopCat.{u}} {hσ : ∀ j : Fin (n + 1), IsClosedEmbedding (X.σ j)}
  {inl : (skeleton X).obj n ⟶ Z} {inr : TopCat.of (X _⦋n + 1⦌ × toTop.{u}.obj ⦋n + 1⦌) ⟶ Z}

private def skeletonSuccComponent (inl : (skeleton X).obj n ⟶ Z)
    (inr : TopCat.of (X _⦋n + 1⦌ × toTop.{u}.obj ⦋n + 1⦌) ⟶ Z) (k : ℕ) (hk : k ≤ n + 1) :
    C(X _⦋k⦌ × toTop.{u}.obj ⦋k⦌, Z) :=
  if h : k ≤ n then inl.hom.comp (skeleton.ι X n h) else (by omega : k = n + 1) ▸ inr.hom

variable (hw : attachingMap X n hσ ≫ inl = TopCat.ofHom ⟨Subtype.val, continuous_subtypeVal⟩ ≫ inr)
include hw

private theorem pushout_rel_le_succ {l : ℕ} (hl : l ≤ n) (f : ⦋l⦌ ⟶ ⦋n + 1⦌) (x : X _⦋n + 1⦌)
    (u : toTop.{u}.obj ⦋l⦌) :
    inl (skeleton.ι X n hl (X.map f.op x, u)) = inr (x, toTop.map f u) := by
  have hmem : (x, toTop.map f u) ∈ attachingSet X (n + 1) := Or.inr ⟨trivial,
    toTop_map_mem_toTopBoundary_of_len_lt f (Nat.lt_succ_of_le hl) u⟩
  exact (congrArg inl (attachingFun_map_right X hl f x u hmem).symm).trans
    (ConcreteCategory.congr_hom hw ⟨(x, toTop.map f u), hmem⟩)

private theorem pushout_rel_succ_le {k : ℕ} (hk : k ≤ n) (f : ⦋n + 1⦌ ⟶ ⦋k⦌) (x : X _⦋k⦌)
    (u : toTop.{u}.obj ⦋n + 1⦌) :
    inr (X.map f.op x, u) = inl (skeleton.ι X n hk (x, toTop.map f u)) := by
  have hmem : (X.map f.op x, u) ∈ attachingSet X (n + 1) :=
    Or.inl ⟨⟨k, Nat.lt_succ_of_le hk, f, x, rfl⟩, trivial⟩
  exact (ConcreteCategory.congr_hom hw ⟨(X.map f.op x, u), hmem⟩).symm.trans
    (congrArg inl (attachingFun_map_left X hk f x u hmem))

private theorem pushout_rel_succ_succ (f : ⦋n + 1⦌ ⟶ ⦋n + 1⦌) (x : X _⦋n + 1⦌)
    (u : toTop.{u}.obj ⦋n + 1⦌) : inr (X.map f.op x, u) = inr (x, toTop.map f u) := by
  by_cases hiso : IsIso f
  · obtain rfl := eq_id_of_isIso f
    rw [op_id, X.map_id, toTop.map_id, TopCat.id_app, TopCat.id_app]
  · let r := (Limits.image f).len
    have hr : r ≤ n := by
      have hle : r ≤ n + 1 := le_of_mono (Limits.image.ι f)
      by_contra hgt; have hlen : r = n + 1 := by omega
      have := (isIso_iff_of_mono (Limits.image.ι f)).mpr hlen
      have := (isIso_iff_of_epi (Limits.factorThruImage f)).mpr hlen.symm
      exact hiso (Limits.image.fac f ▸ inferInstance)
    calc inr (X.map f.op x, u)
      _ = inr (X.map (Limits.factorThruImage f).op (X.map (Limits.image.ι f).op x), u) := by
          rw [map_op_comp_apply X, Limits.image.fac f]
      _ = inl (skeleton.ι X n hr
            (X.map (Limits.image.ι f).op x, toTop.map (Limits.factorThruImage f) u)) :=
          pushout_rel_succ_le X hw hr (Limits.factorThruImage f) _ u
      _ = inr (x, toTop.map f u) := by
          rw [pushout_rel_le_succ X hw hr (Limits.image.ι f) x _, toTop_map_comp_apply,
            Limits.image.fac f]

private def skeletonSuccDesc : (skeleton X).obj (n + 1) ⟶ Z :=
  ConcreteCategory.ofHom (C := TopCat) <|
    skeleton.desc X (n + 1) (skeletonSuccComponent X inl inr) fun l k hl hk f x u ↦ by
      by_cases hl' : l ≤ n <;> by_cases hk' : k ≤ n
      · simp [skeletonSuccComponent, hl', hk', skeleton.ι_map X n hl' hk' f x u]
      · obtain rfl : k = n + 1 := by omega
        simpa [skeletonSuccComponent, hl', hk'] using pushout_rel_le_succ X hw hl' f x u
      · obtain rfl : l = n + 1 := by omega
        simpa [skeletonSuccComponent, hl', hk'] using pushout_rel_succ_le X hw hk' f x u
      · obtain rfl : l = n + 1 := (by omega); obtain rfl : k = n + 1 := by omega
        simpa [skeletonSuccComponent, hl'] using pushout_rel_succ_succ X hw f x u

private theorem skeletonSuccDesc_ι_of_le {k : ℕ} (hk' : k ≤ n + 1) (hk : k ≤ n)
    (p : X _⦋k⦌ × toTop.{u}.obj ⦋k⦌) :
    skeletonSuccDesc X hw (skeleton.ι X (n + 1) hk' p) = inl (skeleton.ι X n hk p) := by
  simp [skeletonSuccDesc, skeletonSuccComponent, hk]

@[simp] private theorem skeletonSuccDesc_ι_succ (hk : n + 1 ≤ n + 1)
    (p : X _⦋n + 1⦌ × toTop.{u}.obj ⦋n + 1⦌) :
    skeletonSuccDesc X hw (skeleton.ι X (n + 1) hk p) = inr p := by
  have hn : ¬ n + 1 ≤ n := by omega
  simp [skeletonSuccDesc, skeletonSuccComponent, hn]

end PushoutDesc

/-- **Skeletal pushout theorem.** When all degeneracies `X.σ j` in degree `n` are closed embeddings,
stage `n + 1` of the skeletal filtration is the pushout in `TopCat` of stage `n` and
`X _⦋n + 1⦌ × Δⁿ⁺¹` along the closed attaching subspace `attachingSet X (n + 1)`. -/
theorem isPushout_skeleton_succ (n : ℕ) (hσ : ∀ j : Fin (n + 1), IsClosedEmbedding (X.σ j)) :
    IsPushout (attachingMap X n hσ) (TopCat.ofHom ⟨Subtype.val, continuous_subtypeVal⟩)
      ((skeleton X).map (homOfLE (Nat.le_succ n))) (skeleton.ιHom X (n + 1) le_rfl) := by
  have w := attachingMap_comp_skeleton_map X n hσ
  refine IsPushout.of_isColimit' ⟨w⟩ (PushoutCocone.IsColimit.mk w
    (fun s ↦ skeletonSuccDesc X s.condition)
    (fun s ↦ by ext k hk x t; simp [skeletonSuccDesc_ι_of_le X s.condition _ hk])
    (fun s ↦ TopCat.ext fun p ↦ skeletonSuccDesc_ι_succ X s.condition le_rfl p)
    fun s m hinl hinr ↦ ?_)
  ext k hk x t; by_cases hk' : k ≤ n
  · simpa only [TopCat.coe_comp, Function.comp_apply, skeleton.map_ι,
      ← skeletonSuccDesc_ι_of_le X s.condition hk hk'] using
      ConcreteCategory.congr_hom hinl (skeleton.ι X n hk' (x, t))
  · obtain rfl : k = n + 1 := by omega
    exact (ConcreteCategory.congr_hom hinr (x, t)).trans
      (skeletonSuccDesc_ι_succ X s.condition hk (x, t)).symm

end Pushout

section Topology

private theorem preimage_ι_singleton_eq_iUnion (p : X.geometricRealization) (n : ℕ) :
    ι X n ⁻¹' {p} =
      ⋃ (m : Fin (n + 1)) (μ : ⦋m.val⦌ ⟶ ⦋n⦌) (_ : Mono μ) (π : ⦋m.val⦌ ⟶ ⦋(normalForm X p).dim⦌),
        {x | X.map μ.op x = X.map π.op (normalForm X p).simplex.val} ×ˢ
          (toTop.map μ '' (toTop.map π ⁻¹' {(normalForm X p).point.val})) := by
  ext ⟨x, t⟩; simp only [mem_iUnion, mem_preimage, mem_singleton_iff, prodMk_mem_set_prod_eq,
    mem_ofPred_eq, mem_image]; constructor
  · intro hp
    rcases hp ▸ isNormalForm_normalForm_ι X x t with ⟨k, μ, hμ, u, _, π, _, ht, hx, hp'⟩
    exact ⟨⟨k, Nat.lt_succ_of_le (le_of_mono μ)⟩, μ, hμ, π, hx, u, hp', ht⟩
  · rintro ⟨m, μ, _, π, hx, u, hu, rfl⟩
    rw [← ι_map, hx, ι_map, hu]; exact toRealization_normalForm X p

private theorem isClosed_preimage_ι_singleton (p : X.geometricRealization) (n : ℕ)
    [hT : ∀ k : {k : ℕ // k ≤ n}, T1Space (X _⦋k.val⦌)] : IsClosed (ι X n ⁻¹' {p}) := by
  rw [preimage_ι_singleton_eq_iUnion X p n]
  refine isClosed_iUnion_of_finite fun m ↦ isClosed_iUnion_of_finite fun μ ↦
    isClosed_iUnion_of_finite fun _ ↦ isClosed_iUnion_of_finite fun π ↦ ?_
  have := hT ⟨m.val, Nat.lt_succ_iff.mp m.isLt⟩
  exact (isClosed_singleton.preimage (X.map μ.op).hom.continuous).prod <|
    (isClosedEmbedding_toTop_map_of_mono μ).isClosedMap _
      (isClosed_singleton.preimage (toTop.map π).hom.continuous)

/-- If each level `X _⦋n⦌` is `T1`, then `|X|` is `T1` in its colimit topology. -/
instance instT1Space [∀ n : ℕ, T1Space (X _⦋n⦌)] : T1Space X.geometricRealization :=
  ⟨fun p ↦ (isClosed_iff X).mpr fun n ↦ isClosed_preimage_ι_singleton X p n⟩

/-- If each level `X _⦋k⦌` (`k ≤ n`) is `T1`, stage `skₙ |X|` of the skeletal filtration is `T1`. -/
instance instT1SpaceSkeleton (n : ℕ) [hT : ∀ k : {k : ℕ // k ≤ n}, T1Space (X _⦋k.val⦌)] :
    T1Space ((skeleton X).obj n) := ⟨fun q ↦ (skeleton.isClosed_iff X).mpr fun k hk ↦ by
  have : ∀ m : {m : ℕ // m ≤ k}, T1Space (X _⦋m.val⦌) := fun m ↦ hT ⟨m.val, m.property.trans hk⟩
  have hpre : skeleton.ι X n hk ⁻¹' {q} = ι X k ⁻¹' {skeleton.toRealization X n q} := by
    ext p; simp [← (skeleton.toRealization_injective X n).eq_iff]
  rw [hpre]; exact isClosed_preimage_ι_singleton X (skeleton.toRealization X n q) k⟩

/-- Every compact subset of `|X|` lies in a single skeleton `skₙ |X|` whenever each `X _⦋n⦌` is
`T1`, with no hypothesis on degeneracies. -/
theorem exists_subset_range_skeleton_toRealization_of_isCompact [∀ n : ℕ, T1Space (X _⦋n⦌)]
    {K : Set X.geometricRealization} (hK : IsCompact K) :
    ∃ n : ℕ, K ⊆ range (skeleton.toRealization X n) :=
  TauCeti.TopCat.exists_subset_range_ι_of_isCompact
    (fun _ _ hij ↦ skeleton_map_injective X hij) (isColimitSkeletonCocone X) hK

/-- If all degeneracies in degree `n` are closed embeddings, `skₙ |X| ⟶ skₙ₊₁ |X|` is a closed
embedding. -/
theorem isClosedEmbedding_skeleton_map_succ {n : ℕ}
    (hσ : ∀ j : Fin (n + 1), IsClosedEmbedding (X.σ j)) :
    IsClosedEmbedding ((skeleton X).map (homOfLE n.le_succ)) :=
  TauCeti.TopCat.isClosedEmbedding_of_isPushout (isPushout_skeleton_succ X n hσ)
    (isClosed_attachingSet X (X.isClosed_degenerate_succ hσ)).isClosedEmbedding_subtypeVal

/-- If all degeneracies in degrees `m ≤ k < n` are closed embeddings, `skₘ |X| ⟶ skₙ |X|` is a
closed embedding. -/
theorem isClosedEmbedding_skeleton_map {m n : ℕ} (hmn : m ≤ n)
    (hσ : ∀ {k : ℕ}, m ≤ k → k < n → ∀ j : Fin (k + 1), IsClosedEmbedding (X.σ j)) :
    IsClosedEmbedding ((skeleton X).map (homOfLE hmn)) := by
  induction n, hmn using Nat.le_induction with
  | base => rw [Subsingleton.elim (homOfLE (le_refl m)) (𝟙 m), (skeleton X).map_id]; exact .id
  | succ n hmn ih =>
    rw [← homOfLE_comp hmn n.le_succ, (skeleton X).map_comp]
    exact (isClosedEmbedding_skeleton_map_succ X (hσ hmn (Nat.lt_succ_self n))).comp
      (ih fun h1 h2 ↦ hσ h1 (Nat.lt_succ_of_lt h2))

/-- If each `X _⦋k⦌ × Δᵏ` (`k ≤ n`) is normal and all degeneracies in degrees `k < n` are closed
embeddings, stage `skₙ |X|` is normal. -/
theorem normalSpace_skeleton (n : ℕ)
    (hσ : ∀ {k : ℕ}, k < n → ∀ j : Fin (k + 1), IsClosedEmbedding (X.σ j))
    [hN : ∀ k : {k : ℕ // k ≤ n}, NormalSpace (X _⦋k.val⦌ × toTop.{u}.obj ⦋k.val⦌)] :
    NormalSpace ((skeleton X).obj n) := by
  revert hN; induction n with
  | zero =>
    intro hN; have := hN ⟨0, le_rfl⟩
    have := (Homeomorph.prodUnique (X _⦋0⦌) (toTop.{u}.obj ⦋0⦌)).normalSpace
    exact (TopCat.homeoOfIso (skeletonZeroIso X)).symm.normalSpace
  | succ n ih =>
    intro hN; have := hN ⟨n + 1, le_rfl⟩
    have : ∀ k : {k : ℕ // k ≤ n}, NormalSpace (X _⦋k.val⦌ × toTop.{u}.obj ⦋k.val⦌) :=
      fun k ↦ hN ⟨k.val, k.property.trans n.le_succ⟩
    have := ih fun hk ↦ hσ (Nat.lt_succ_of_lt hk); have hσn := hσ (Nat.lt_succ_self n)
    exact TauCeti.TopCat.normalSpace_of_isPushout (isPushout_skeleton_succ X n hσn)
      (isClosed_attachingSet X (X.isClosed_degenerate_succ hσn)).isClosedEmbedding_subtypeVal

section ClosedDegeneracies

variable (hσ : ∀ {n : ℕ} (j : Fin (n + 1)), IsClosedEmbedding (X.σ j))
include hσ

/-- If all degeneracies of `X` are closed embeddings, every stage inclusion `skₙ |X| ⟶ |X|` is a
closed embedding. -/
theorem isClosedEmbedding_skeleton_toRealization (n : ℕ) :
    IsClosedEmbedding (skeleton.toRealization X n) :=
  TauCeti.TopCat.isClosedEmbedding_ι_of_isColimit_of_succ
    (fun _ ↦ isClosedEmbedding_skeleton_map_succ X hσ) (isColimitSkeletonCocone X) n

/-- Every continuous map from a compact space into `|X|` factors continuously through a single
skeleton `skₙ |X|` when each `X _⦋n⦌` is `T1` and all degeneracies are closed embeddings. -/
theorem exists_lift_skeleton_of_compactSpace [∀ n : ℕ, T1Space (X _⦋n⦌)]
    {K : Type*} [TopologicalSpace K] [CompactSpace K] (g : C(K, X.geometricRealization)) :
    ∃ (n : ℕ) (g' : C(K, (skeleton X).obj n)), (skeleton.toRealization X n).hom.comp g' = g :=
  TauCeti.TopCat.exists_lift_of_compactSpace (isColimitSkeletonCocone X)
    (fun n ↦ (isClosedEmbedding_skeleton_toRealization X hσ n).isEmbedding) g

/-- If each `X _⦋n⦌ × Δⁿ` is normal and all degeneracies are closed embeddings, `|X|` is normal in
its colimit topology. -/
theorem normalSpace [∀ n : ℕ, NormalSpace (X _⦋n⦌ × toTop.{u}.obj ⦋n⦌)] :
    NormalSpace X.geometricRealization := by
  have := fun n ↦ normalSpace_skeleton X n (fun _ ↦ hσ)
  exact TauCeti.TopCat.normalSpace_of_isColimit
    (fun _ ↦ isClosedEmbedding_skeleton_map_succ X hσ) (isColimitSkeletonCocone X)

end ClosedDegeneracies

/-- **Separation of thin geometric realization.** If each `X _⦋n⦌ × Δⁿ` is `T4`, `|X|` is `T4` —
and hence Hausdorff, and paracompact whenever each `X _⦋n⦌ × Δⁿ` is Lindelöf — in its actual
colimit topology. -/
instance instT4Space [∀ n : ℕ, T4Space (X _⦋n⦌ × toTop.{u}.obj ⦋n⦌)] :
    T4Space X.geometricRealization := by
  have : ∀ n : ℕ, T2Space (X _⦋n⦌) :=
    fun n ↦ (isEmbedding_prodMkLeft (toTopInitialVertex.{u} ⦋n⦌)).t2Space
  have : NormalSpace X.geometricRealization := normalSpace X fun {n} j ↦ X.isClosedEmbedding_σ j
  exact {}

/-- Every simplicial space whose levels `X _⦋n⦌` are `T3` (regular Hausdorff) and Lindelöf has a
`T4` (normal Hausdorff, and hence paracompact) thin geometric realization in its colimit
topology. -/
instance (priority := 90) instT4Space_of_t3Space_lindelofSpace [h3 : ∀ n : ℕ, T3Space (X _⦋n⦌)]
    [hL : ∀ n : ℕ, LindelofSpace (X _⦋n⦌)] : T4Space X.geometricRealization :=
  have (n : ℕ) : T4Space (X _⦋n⦌ × toTop.{u}.obj ⦋n⦌) :=
    have := h3 n
    have := hL n
    inferInstance
  inferInstance

end Topology

end CategoryTheory.SimplicialObject.geometricRealization
