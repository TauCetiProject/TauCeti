/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
public import TauCeti.AlgebraicTopology.SimplicialObject.GeometricRealization.Basic
public import TauCeti.AlgebraicTopology.SimplicialObject.TopCat
public import TauCeti.Topology.Category.TopCat.Compact
public import TauCeti.Topology.Category.TopCat.Paracompact

/-!
# Normal form, skeletal filtration, and point-set topology of thin geometric realization

Every point of `X.geometricRealization` decomposes uniquely into a dimension `d`, a nondegenerate
`d`-simplex of `X ⋙ forget TopCat`, and a point of `toTopInterior ⦋d⦌`
(`geometricRealization.Cell.realizationEquiv`). Consequently, any levelwise injective morphism
(respectively closed embedding) `φ : Y ⟶ X` induces an injective map (respectively closed embedding)
`|φ| : |Y| ⟶ |X|` with no backwards-closure hypothesis (`geometricRealization.map_injective`,
`geometricRealization.isClosedEmbedding_map`), and whenever every `X _⦋n⦌` is `T1`, `|X|` is `T1`
and compact subsets factor through a single stage of `geometricRealization.skeleton X`.

When all degeneracies `X.σ j` are closed embeddings, stage `n + 1` of `skeleton X` is the pushout
of stage `n` and `X _⦋n + 1⦌ × Δⁿ⁺¹` along the closed subspace `geometricRealization.attachingSet`
(`geometricRealization.isPushout_skeleton_succ`). Hence every stage inclusion is a closed embedding,
and whenever each `X _⦋n⦌` is `T1` and each `X _⦋n⦌ × Δⁿ` is normal, `X.geometricRealization` is
`T4` — hence Hausdorff, and paracompact when Lindelöf — in its colimit topology
(`geometricRealization.instT4Space`).

## References

* J. Milnor, *The geometric realization of a semi-simplicial complex*, Ann. of Math. **65** (1957).
* J. P. May, *The Geometry of Iterated Loop Spaces*, LNM **271**, Springer, 1972, §11.1–11.2.
* G. Segal, *Categories and cohomology theories*, Topology **13** (1974), 293–312, Appendix A.
-/

public noncomputable section

open CategoryTheory Limits Opposite Set Simplicial Topology

universe u

namespace CategoryTheory.SimplicialObject.geometricRealization

open SimplexCategory (toTop toTopInterior toTopBoundary)

variable (X : SimplicialObject TopCat.{u})

section NormalForm

/-- An interior cell of a simplicial space `X`: a dimension `d`, a nondegenerate `d`-simplex of
`X ⋙ forget TopCat`, and a point in the open interior of `Δᵈ`. -/
@[ext]
structure Cell : Type u where
  /-- Dimension of the cell. -/
  dim : ℕ
  /-- Nondegenerate simplex indexing the cell. -/
  simplex : SSet.nonDegenerate (X ⋙ forget TopCat) dim
  /-- Interior coordinates in the standard topological simplex `Δᵈ`. -/
  point : toTopInterior.{u} ⦋dim⦌

/-- The point of `X.geometricRealization` represented by an interior cell. -/
def Cell.toRealization (c : Cell X) : X.geometricRealization :=
  ι X c.dim (c.simplex.1, c.point.1)

private def IsNormalForm {n : ℕ} (x : X _⦋n⦌) (t : toTop.{u}.obj ⦋n⦌) (c : Cell X) : Prop :=
  ∃ (k : ℕ) (μ : ⦋k⦌ ⟶ ⦋n⦌) (_ : Mono μ) (u : toTop.{u}.obj ⦋k⦌)
    (_ : u ∈ toTopInterior.{u} ⦋k⦌) (π : ⦋k⦌ ⟶ ⦋c.dim⦌) (_ : Epi π),
    toTop.map μ u = t ∧ X.map μ.op x = X.map π.op c.simplex.1 ∧ toTop.map π u = c.point.1

private theorem exists_isNormalForm {n : ℕ} (x : X _⦋n⦌) (t : toTop.{u}.obj ⦋n⦌) :
    ∃ c : Cell X, IsNormalForm X x t c := by
  obtain ⟨k, μ, hμ, u, hu, rfl⟩ := SimplexCategory.exists_mono_toTop_map_mem_toTopInterior t
  obtain ⟨d, π, hπ, y, hy⟩ := SSet.exists_nonDegenerate (X := X ⋙ forget TopCat) (X.map μ.op x)
  exact ⟨⟨d, y, ⟨toTop.map π u, SimplexCategory.toTop_map_mem_toTopInterior_of_epi π hu⟩⟩,
    k, μ, hμ, u, hu, π, hπ, rfl, hy, rfl⟩

private theorem IsNormalForm.unique {X : SimplicialObject TopCat.{u}} {n : ℕ} {x : X _⦋n⦌}
    {t : toTop.{u}.obj ⦋n⦌} {c₁ c₂ : Cell X} (h₁ : IsNormalForm X x t c₁)
    (h₂ : IsNormalForm X x t c₂) : c₁ = c₂ := by
  rcases h₁ with ⟨k₁, μ₁, _, u₁, hu₁, π₁, _, ht₁, hx₁, hp₁⟩
  rcases h₂ with ⟨k₂, μ₂, _, u₂, hu₂, π₂, _, ht₂, hx₂, hp₂⟩
  obtain rfl := SimplexCategory.unique_mono_toTop_map_dim hu₁ hu₂ (ht₁.trans ht₂.symm)
  obtain rfl := SimplexCategory.unique_mono_toTop_map_hom hu₁ (ht₁.trans ht₂.symm)
  obtain rfl := SimplexCategory.toTop_map_injective_of_mono μ₁ (ht₁.trans ht₂.symm)
  rcases c₁ with ⟨d₁, y₁, p₁⟩; rcases c₂ with ⟨d₂, y₂, p₂⟩
  dsimp only at π₁ π₂ hx₁ hx₂ hp₁ hp₂
  obtain rfl : d₁ = d₂ := SSet.unique_nonDegenerate_dim (X := X ⋙ forget TopCat)
    (X.map μ₁.op x) π₁ y₁ hx₁ π₂ y₂ hx₂
  obtain rfl : y₁ = y₂ := SSet.unique_nonDegenerate_simplex (X := X ⋙ forget TopCat)
    (X.map μ₁.op x) π₁ y₁ hx₁ π₂ y₂ hx₂
  obtain rfl : π₁ = π₂ := SSet.unique_nonDegenerate_map (X := X ⋙ forget TopCat)
    (X.map μ₁.op x) π₁ y₁ hx₁ π₂ y₁ hx₂
  exact congrArg (Cell.mk d₁ y₁) (Subtype.ext (hp₁.symm.trans hp₂))

private theorem IsNormalForm.self (c : Cell X) : IsNormalForm X c.simplex.1 c.point.1 c :=
  ⟨c.dim, 𝟙 ⦋c.dim⦌, inferInstance, c.point.1, c.point.2, 𝟙 ⦋c.dim⦌, inferInstance,
    by rw [toTop.map_id, TopCat.id_app], rfl, by rw [toTop.map_id, TopCat.id_app]⟩

private theorem IsNormalForm.of_map {X : SimplicialObject TopCat.{u}} {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    (x : X _⦋n⦌) (u₀ : toTop.{u}.obj ⦋m⦌) {c : Cell X}
    (hc : IsNormalForm X x (toTop.map f u₀) c) : IsNormalForm X (X.map f.op x) u₀ c := by
  obtain ⟨k, μ_u, _, u₁, hu₁, rfl⟩ := SimplexCategory.exists_mono_toTop_map_mem_toTopInterior u₀
  let g := μ_u ≫ f
  let p : ⦋k⦌ ⟶ ⦋(Limits.image g).len⦌ := Limits.factorThruImage g
  let μ_t : ⦋(Limits.image g).len⦌ ⟶ ⦋n⦌ := Limits.image.ι g
  have hfac : p ≫ μ_t = μ_u ≫ f := Limits.image.fac g
  have hu₂ := SimplexCategory.toTop_map_mem_toTopInterior_of_epi p hu₁
  have ht₂ : toTop.map μ_t (toTop.map p u₁) = toTop.map f (toTop.map μ_u u₁) := by
    rw [← TopCat.comp_app, ← toTop.map_comp, hfac, toTop.map_comp, TopCat.comp_app]
  rcases hc with ⟨k', μ', _, u', hu', π', _, ht', hx', hp'⟩
  obtain rfl := SimplexCategory.unique_mono_toTop_map_dim hu₂ hu' (ht₂.trans ht'.symm)
  obtain rfl := SimplexCategory.unique_mono_toTop_map_hom hu₂ (ht₂.trans ht'.symm)
  obtain rfl := SimplexCategory.toTop_map_injective_of_mono μ_t (ht₂.trans ht'.symm)
  refine ⟨k, μ_u, inferInstance, u₁, hu₁, p ≫ π', epi_comp p π', rfl, ?_, ?_⟩
  · rw [← TopCat.comp_app, ← X.map_comp, ← op_comp, ← hfac, op_comp, X.map_comp,
      TopCat.comp_app, hx', ← TopCat.comp_app, ← X.map_comp, ← op_comp]
  · rw [toTop.map_comp, TopCat.comp_app, hp']

/-- The canonical interior cell associated to a point of `X.geometricRealization`. -/
def normalForm : X.geometricRealization → Cell X :=
  descFun (fun _ p ↦ (exists_isNormalForm X p.1 p.2).choose) fun _ _ f x t ↦
    (exists_isNormalForm X (X.map f.op x) t).choose_spec.unique
      (IsNormalForm.of_map f x t (exists_isNormalForm X x (toTop.map f t)).choose_spec)

private theorem isNormalForm_normalForm_ι {n : ℕ} (x : X _⦋n⦌) (t : toTop.{u}.obj ⦋n⦌) :
    IsNormalForm X x t (normalForm X (ι X n (x, t))) := by
  rw [normalForm, descFun_ι]; exact (exists_isNormalForm X x t).choose_spec

@[simp]
theorem normalForm_toRealization (c : Cell X) : normalForm X (c.toRealization X) = c :=
  (isNormalForm_normalForm_ι X c.simplex.1 c.point.1).unique (IsNormalForm.self X c)

@[simp]
theorem toRealization_normalForm (p : X.geometricRealization) :
    (normalForm X p).toRealization X = p := by
  obtain ⟨n, x, t, rfl⟩ := ι_jointly_surjective X p
  rcases isNormalForm_normalForm_ι X x t with ⟨k, μ, _, u, _, π, _, ht, hx, hp⟩
  rw [Cell.toRealization, ← hp, ← ι_map, ← hx, ι_map, ht]

/-- **Canonical cell decomposition of thin geometric realization.** Every point of `|X|` is
represented by a unique nondegenerate simplex together with a point in the open simplex interior. -/
def Cell.realizationEquiv : Cell X ≃ X.geometricRealization where
  toFun := Cell.toRealization X
  invFun := normalForm X
  left_inv := normalForm_toRealization X
  right_inv := toRealization_normalForm X

end NormalForm

section MapEmbedding

variable {X} {Y : SimplicialObject TopCat.{u}} {φ : Y ⟶ X}

private theorem nonDegenerate_of_injective_map
    (hinj : ∀ n : ℕ, Function.Injective (φ.app (op ⦋n⦌))) {n : ℕ} {y : Y _⦋n⦌}
    (hy : y ∈ SSet.nonDegenerate (Y ⋙ forget TopCat) n) :
    φ.app (op ⦋n⦌) y ∈ SSet.nonDegenerate (X ⋙ forget TopCat) n := by
  rw [SSet.mem_nonDegenerate_iff_notMem_degenerate] at hy ⊢
  cases n with
  | zero => simp [SSet.degenerate_zero]
  | succ m =>
    rw [SSet.degenerate_eq_iUnion_range_σ, Set.mem_iUnion]
    rintro ⟨j, x', hx'⟩
    have hx'_eq : x' = φ.app (op ⦋m⦌) (Y.δ j.castSucc y) :=
      calc x' = (X.σ j ≫ X.δ j.castSucc) x' := by rw [X.δ_comp_σ_self, TopCat.id_app]
        _ = X.δ j.castSucc (φ.app (op ⦋m + 1⦌) y) := congrArg (X.δ j.castSucc) hx'
        _ = φ.app (op ⦋m⦌) (Y.δ j.castSucc y) :=
            (NatTrans.naturality_apply φ (SimplexCategory.δ j.castSucc).op y).symm
    have hσ := (NatTrans.naturality_apply φ (SimplexCategory.σ j).op _).trans
      ((congrArg (X.σ j) hx'_eq.symm).trans hx')
    exact hy (SSet.degenerate_eq_iUnion_range_σ (Y ⋙ forget TopCat) ▸
      Set.mem_iUnion.mpr ⟨j, Y.δ j.castSucc y, hinj (m + 1) hσ⟩)

private abbrev mapCell (hinj : ∀ n : ℕ, Function.Injective (φ.app (op ⦋n⦌))) (c : Cell Y) :
    Cell X :=
  ⟨c.dim, ⟨φ.app (op ⦋c.dim⦌) c.simplex.1, nonDegenerate_of_injective_map hinj c.simplex.2⟩,
    c.point⟩

private theorem normalForm_map (hinj : ∀ n : ℕ, Function.Injective (φ.app (op ⦋n⦌)))
    (q : Y.geometricRealization) : normalForm X (map φ q) = mapCell hinj (normalForm Y q) := by
  conv_lhs => rw [← toRealization_normalForm Y q]
  exact (map_ι φ _ _ _) ▸ normalForm_toRealization X (mapCell hinj (normalForm Y q))

/-- **Injectivity for thin geometric realization.** Any levelwise injective morphism `φ : Y ⟶ X`
of simplicial spaces induces an injective map `|φ| : |Y| ⟶ |X|`, with no backwards-closure
hypothesis. -/
theorem map_injective (hinj : ∀ n : ℕ, Function.Injective (φ.app (op ⦋n⦌))) :
    Function.Injective (map φ) := fun q₁ q₂ h ↦ by
  have hc := (normalForm_map hinj q₁).symm.trans ((congrArg (normalForm X) h).trans
    (normalForm_map hinj q₂))
  rcases h₁ : normalForm Y q₁ with ⟨d₁, y₁, p₁⟩
  rcases h₂ : normalForm Y q₂ with ⟨d₂, y₂, p₂⟩
  rw [h₁, h₂] at hc
  obtain rfl : d₁ = d₂ := congrArg Cell.dim hc
  injection hc with _ hsimp hp
  have hy : y₁ = y₂ := Subtype.ext (hinj d₁ (congrArg Subtype.val hsimp))
  exact (toRealization_normalForm Y q₁).symm.trans <|
    (congrArg (Cell.toRealization Y) (by rw [h₁, h₂, hy]; exact congrArg _ hp)).trans
      (toRealization_normalForm Y q₂)

private theorem preimage_ι_image_map_eq_iUnion
    (hinj : ∀ n : ℕ, Function.Injective (φ.app (op ⦋n⦌)))
    (W : Set Y.geometricRealization) (n : ℕ) :
    ι X n ⁻¹' (map φ '' W) =
      ⋃ (m : Fin (n + 1)) (μ : ⦋m.1⦌ ⟶ ⦋n⦌) (_ : Mono μ),
        Prod.map id (toTop.map μ) '' (Prod.map (X.map μ.op) id ⁻¹'
          (Prod.map (φ.app (op ⦋m.1⦌)) id '' (ι Y m.1 ⁻¹' W))) := by
  ext ⟨x, t⟩; simp only [Set.mem_iUnion]; constructor
  · rintro ⟨q, hq, hqx⟩
    have hnf : normalForm X (ι X n (x, t)) = mapCell hinj (normalForm Y q) :=
      hqx ▸ normalForm_map hinj q
    rcases hnf ▸ isNormalForm_normalForm_ι X x t with ⟨k, μ, hμ, u, _, π, _, ht, hx, hp⟩
    let y : Y _⦋k⦌ := Y.map π.op (normalForm Y q).simplex.1
    have hiy : ι Y k (y, u) = q :=
      (ι_map Y π _ u).trans (hp.symm ▸ toRealization_normalForm Y q)
    exact ⟨⟨k, Nat.lt_succ_of_le (SimplexCategory.le_of_mono μ)⟩, μ, hμ, (x, u),
      ⟨(y, u), (congrArg (· ∈ W) hiy).mpr hq,
        Prod.ext ((NatTrans.naturality_apply φ π.op _).trans hx.symm) rfl⟩,
      Prod.ext rfl ht⟩
  · rintro ⟨m, μ, _, ⟨_, _⟩, ⟨⟨y, u⟩, hyW, hxy⟩, hxt⟩
    simp only [Prod.map_apply, id_eq, Prod.mk.injEq] at hxy hxt
    obtain ⟨hφy, rfl⟩ := hxy; obtain ⟨rfl, rfl⟩ := hxt
    exact ⟨ι Y m.1 (y, u), hyW, by change map φ (ι Y m.1 (y, u)) = _; rw [map_ι, hφy, ι_map]⟩

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
  exact (IsClosedEmbedding.id.prodMap
    (SimplexCategory.isClosedEmbedding_toTop_map_of_mono μ)).isClosedMap _ <|
    (((hφ m.1).prodMap .id).isClosedMap _ ((isClosed_iff Y).mp hW m.1)).preimage
      (((X.map μ.op).hom.continuous.comp continuous_fst).prodMk continuous_snd)

end MapEmbedding

section Skeleton

private inductive SkeletonRel (n : ℕ) :
    (Σ k : {k : ℕ // k ≤ n}, X _⦋k.1⦌ × toTop.{u}.obj ⦋k.1⦌) →
      (Σ k : {k : ℕ // k ≤ n}, X _⦋k.1⦌ × toTop.{u}.obj ⦋k.1⦌) → Prop where
  | mk {l k : ℕ} (hl : l ≤ n) (hk : k ≤ n) (f : ⦋l⦌ ⟶ ⦋k⦌) (x : X _⦋k⦌) (t : toTop.{u}.obj ⦋l⦌) :
      SkeletonRel n ⟨⟨l, hl⟩, X.map f.op x, t⟩ ⟨⟨k, hk⟩, x, toTop.map f t⟩

/-- The `n`-skeleton `skₙ |X|` of `X.geometricRealization`: the quotient of `Σ k ≤ n, X _⦋k⦌ × Δᵏ`
by the simplicial identifications in degrees at most `n`. -/
def skeletonObj (n : ℕ) : TopCat.{u} := TopCat.of (Quot (SkeletonRel X n))

/-- Characteristic map `X _⦋k⦌ × Δᵏ → skₙ |X|` for `k ≤ n`. -/
def skeleton.ι (n : ℕ) {k : ℕ} (hk : k ≤ n) : C(X _⦋k⦌ × toTop.{u}.obj ⦋k⦌, skeletonObj X n) :=
  ⟨fun p ↦ Quot.mk (SkeletonRel X n) ⟨⟨k, hk⟩, p⟩, continuous_quot_mk.comp continuous_sigmaMk⟩

@[simp]
theorem skeleton.ι_map (n : ℕ) {l k : ℕ} (hl : l ≤ n) (hk : k ≤ n) (f : ⦋l⦌ ⟶ ⦋k⦌)
    (x : X _⦋k⦌) (t : toTop.{u}.obj ⦋l⦌) :
    skeleton.ι X n hl (X.map f.op x, t) = skeleton.ι X n hk (x, toTop.map f t) :=
  Quot.sound (SkeletonRel.mk hl hk f x t)

theorem skeleton.ι_jointly_surjective {n : ℕ} (q : skeletonObj X n) :
    ∃ (k : ℕ) (hk : k ≤ n) (x : X _⦋k⦌) (t : toTop.{u}.obj ⦋k⦌),
      skeleton.ι X n hk (x, t) = q := by
  induction q using Quot.ind with | mk p => exact ⟨p.1.1, p.1.2, p.2.1, p.2.2, rfl⟩

@[ext]
theorem skeleton.hom_ext {n : ℕ} {Z : TopCat.{u}} {g h : skeletonObj X n ⟶ Z}
    (H : ∀ (k : ℕ) (hk : k ≤ n) (x : X _⦋k⦌) (t : toTop.{u}.obj ⦋k⦌),
      g (skeleton.ι X n hk (x, t)) = h (skeleton.ι X n hk (x, t))) : g = h := by
  ext q; obtain ⟨k, hk, x, t, rfl⟩ := skeleton.ι_jointly_surjective X q; exact H k hk x t

/-- Transition map `skₘ |X| ⟶ skₙ |X|` for `m ≤ n`. -/
def skeletonMap {m n : ℕ} (hmn : m ≤ n) : skeletonObj X m ⟶ skeletonObj X n :=
  TopCat.ofHom
    { toFun := Quot.lift (fun p ↦ skeleton.ι X n (p.1.2.trans hmn) p.2) <| by
        rintro _ _ ⟨hl, hk, f, x, t⟩
        exact skeleton.ι_map X n (hl.trans hmn) (hk.trans hmn) f x t
      continuous_toFun := continuous_quot_lift _
        (continuous_sigma fun k ↦ (skeleton.ι X n (k.2.trans hmn)).continuous) }

@[simp]
theorem skeletonMap_ι {m n k : ℕ} (hmn : m ≤ n) (hk : k ≤ m)
    (p : X _⦋k⦌ × toTop.{u}.obj ⦋k⦌) :
    skeletonMap X hmn (skeleton.ι X m hk p) = skeleton.ι X n (hk.trans hmn) p := (rfl)

/-- The skeletal filtration `n ↦ skₙ |X|` of `X.geometricRealization`. -/
@[expose]
def skeleton : ℕ ⥤ TopCat.{u} where
  obj := skeletonObj X
  map f := skeletonMap X (leOfHom f)
  map_id _ := by ext; simp
  map_comp _ _ := by ext; simp

/-- Characteristic morphism `TopCat.of (X _⦋k⦌ × Δᵏ) ⟶ skₙ |X|` in `TopCat` for `k ≤ n`. -/
def skeleton.ιHom (n : ℕ) {k : ℕ} (hk : k ≤ n) :
    TopCat.of (X _⦋k⦌ × toTop.{u}.obj ⦋k⦌) ⟶ (skeleton X).obj n :=
  TopCat.ofHom (skeleton.ι X n hk)

@[simp]
theorem skeleton.ιHom_apply (n : ℕ) {k : ℕ} (hk : k ≤ n) (p : X _⦋k⦌ × toTop.{u}.obj ⦋k⦌) :
    skeleton.ιHom X n hk p = skeleton.ι X n hk p := (rfl)

/-- Stage inclusion morphism `skₙ |X| ⟶ |X|` in `TopCat`. -/
def skeleton.toRealization (n : ℕ) : (skeleton X).obj n ⟶ X.geometricRealization :=
  TopCat.ofHom
    { toFun := Quot.lift (fun p ↦ geometricRealization.ι X p.1.1 p.2) <| by
        rintro _ _ ⟨_, _, f, x, t⟩; exact geometricRealization.ι_map X f x t
      continuous_toFun := continuous_quot_lift _
        (continuous_sigma fun k ↦ (geometricRealization.ι X k.1).continuous) }

@[simp]
theorem skeleton.toRealization_ι (n : ℕ) {k : ℕ} (hk : k ≤ n)
    (p : X _⦋k⦌ × toTop.{u}.obj ⦋k⦌) :
    skeleton.toRealization X n (skeleton.ι X n hk p) = geometricRealization.ι X k p := (rfl)

@[reassoc (attr := simp)]
theorem skeleton_map_comp_toRealization {m n : ℕ} (f : m ⟶ n) :
    (skeleton X).map f ≫ skeleton.toRealization X n = skeleton.toRealization X m :=
  skeleton.hom_ext X fun _ _ _ _ ↦ rfl

instance (n : ℕ) [∀ k : ℕ, LindelofSpace (X _⦋k⦌ × toTop.{u}.obj ⦋k⦌)] :
    LindelofSpace ((skeleton X).obj n) := Quot.lindelofSpace

/-- The canonical cocone exhibiting `X.geometricRealization` above `skeleton X`. -/
@[expose, simps]
def skeletonCocone : Cocone (skeleton X) where
  pt := X.geometricRealization
  ι := { app := skeleton.toRealization X
         naturality _ _ f := (skeleton_map_comp_toRealization X f).trans (Category.comp_id _).symm }

/-- `X.geometricRealization` is the colimit in `TopCat` of its skeletal filtration `skeleton X`. -/
def isColimitSkeletonCocone : IsColimit (skeletonCocone X) where
  desc s := TopCat.ofHom <| desc (Z := s.pt)
    (fun n ↦ (s.ι.app n).hom.comp (skeleton.ιHom X n le_rfl).hom) fun m n f x t ↦ by
      have hm := ConcreteCategory.congr_hom (s.w (homOfLE (le_max_left m n)))
        (skeleton.ιHom X m le_rfl (X.map f.op x, t))
      have hn := ConcreteCategory.congr_hom (s.w (homOfLE (le_max_right m n)))
        (skeleton.ιHom X n le_rfl (x, toTop.map f t))
      exact hm.symm.trans ((congrArg (s.ι.app (max m n))
        (skeleton.ι_map X (max m n) (le_max_left m n) (le_max_right m n) f x t)).trans hn)
  fac s n := skeleton.hom_ext X fun k hk x t ↦
    (desc_ι _ _ k (x, t)).trans
      (ConcreteCategory.congr_hom (s.w (homOfLE hk)) (skeleton.ι X k le_rfl (x, t))).symm
  uniq s m hm := hom_ext X fun n x t ↦
    (ConcreteCategory.congr_hom (hm n) (skeleton.ι X n le_rfl (x, t))).trans
      (desc_ι (Z := s.pt)
        (fun k ↦ (s.ι.app k).hom.comp (skeleton.ιHom X k le_rfl).hom) _ n (x, t)).symm

private theorem skeleton_ι_eq_normalForm {n k : ℕ} (hk : k ≤ n) (x : X _⦋k⦌)
    (t : toTop.{u}.obj ⦋k⦌) {c : Cell X} (hc : IsNormalForm X x t c) :
    ∃ hd : c.dim ≤ n, skeleton.ι X n hk (x, t) = skeleton.ι X n hd (c.simplex.1, c.point.1) := by
  rcases hc with ⟨r, μ, _, u, _, π, _, ht, hx, hp⟩
  have hr : r ≤ n := (SimplexCategory.le_of_mono μ).trans hk
  refine ⟨(SimplexCategory.le_of_epi π).trans hr, ?_⟩
  rw [← ht, ← skeleton.ι_map X n hr hk μ, hx, skeleton.ι_map X n hr _ π, hp]

/-- Every stage inclusion `skₙ |X| ⟶ |X|` is unconditionally injective. -/
theorem skeleton.toRealization_injective (n : ℕ) :
    Function.Injective (skeleton.toRealization X n) := fun q₁ q₂ h ↦ by
  obtain ⟨k₁, hk₁, x₁, t₁, rfl⟩ := skeleton.ι_jointly_surjective X q₁
  obtain ⟨k₂, hk₂, x₂, t₂, rfl⟩ := skeleton.ι_jointly_surjective X q₂
  have hreal : geometricRealization.ι X k₁ (x₁, t₁) = geometricRealization.ι X k₂ (x₂, t₂) := h
  obtain ⟨_, heq₁⟩ := skeleton_ι_eq_normalForm X hk₁ x₁ t₁ (isNormalForm_normalForm_ι X x₁ t₁)
  obtain ⟨_, heq₂⟩ := skeleton_ι_eq_normalForm X hk₂ x₂ t₂
    (hreal ▸ isNormalForm_normalForm_ι X x₂ t₂)
  exact heq₁.trans heq₂.symm

/-- Every skeletal transition map `skₘ |X| ⟶ skₙ |X|` (`m ≤ n`) is unconditionally injective. -/
theorem skeleton_map_injective {m n : ℕ} (hmn : m ≤ n) :
    Function.Injective ((skeleton X).map (homOfLE hmn)) :=
  Function.Injective.of_comp (f := skeleton.toRealization X n) <| by
    rw [← TopCat.coe_comp, skeleton_map_comp_toRealization]
    exact skeleton.toRealization_injective X m

private def skeletonZeroHom : (skeleton X).obj 0 ⟶ X _⦋0⦌ :=
  TopCat.ofHom
    { toFun := Quot.lift (fun p ↦ X.map (SimplexCategory.const ⦋0⦌ ⦋p.1.1⦌ 0).op p.2.1) <| by
        rintro _ _ ⟨hl, hk, f, x, _⟩
        obtain rfl := Nat.eq_zero_of_le_zero hl; obtain rfl := Nat.eq_zero_of_le_zero hk
        obtain rfl : f = 𝟙 ⦋0⦌ := Subsingleton.elim f (𝟙 ⦋0⦌); simp
      continuous_toFun := continuous_quot_lift _ (continuous_sigma fun k ↦
        (X.map (SimplexCategory.const ⦋0⦌ ⦋k.1⦌ 0).op).hom.continuous.comp continuous_fst) }

/-- The `0`-skeleton of `X.geometricRealization` is isomorphic in `TopCat` to `X _⦋0⦌`. -/
def skeletonZeroIso : (skeleton X).obj 0 ≅ X _⦋0⦌ where
  hom := skeletonZeroHom X
  inv := TopCat.ofHom <| (skeleton.ιHom X 0 le_rfl).hom.comp
    ⟨fun x ↦ (x, default), continuous_id.prodMk continuous_const⟩
  hom_inv_id := skeleton.hom_ext X fun k hk x t ↦ by
    obtain rfl := Nat.eq_zero_of_le_zero hk
    obtain rfl : t = default := Subsingleton.elim t default
    change skeleton.ι X 0 le_rfl (X.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op x, default) =
      skeleton.ι X 0 le_rfl (x, default)
    rw [Subsingleton.elim (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0) (𝟙 ⦋0⦌)]; simp
  inv_hom_id := by
    ext x; change X.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op x = x
    rw [Subsingleton.elim (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0) (𝟙 ⦋0⦌)]; simp

end Skeleton

section Pushout

/-- The attaching locus inside `X _⦋n⦌ × Δⁿ`: points whose simplex is degenerate or whose
barycentric coordinates lie in the topological boundary `∂Δⁿ`. -/
def attachingSet (n : ℕ) : Set (X _⦋n⦌ × toTop.{u}.obj ⦋n⦌) :=
  SSet.degenerate (X ⋙ forget TopCat) n ×ˢ Set.univ ∪ Set.univ ×ˢ toTopBoundary.{u} ⦋n⦌

/-- If the degenerate `n`-simplices form a closed subset of `X _⦋n⦌`, the attaching locus is closed
in `X _⦋n⦌ × Δⁿ`. -/
theorem isClosed_attachingSet {n : ℕ}
    (hdeg : IsClosed (X := X _⦋n⦌) (SSet.degenerate (X ⋙ forget TopCat) n)) :
    IsClosed (attachingSet X n) :=
  (hdeg.prod isClosed_univ).union (isClosed_univ.prod (SimplexCategory.isClosed_toTopBoundary ⦋n⦌))

private theorem mem_range_succ_of_mem_attachingSet {n : ℕ}
    {p : X _⦋n + 1⦌ × toTop.{u}.obj ⦋n + 1⦌} (hp : p ∈ attachingSet X (n + 1)) :
    skeleton.ι X (n + 1) le_rfl p ∈ Set.range ((skeleton X).map (homOfLE n.le_succ)) := by
  rcases p with ⟨x, t⟩; rcases hp with ⟨hx, -⟩ | ⟨-, ht⟩
  · obtain ⟨j, y, rfl⟩ :=
      Set.mem_iUnion.mp (SSet.degenerate_eq_iUnion_range_σ (X ⋙ forget TopCat) ▸ hx)
    exact ⟨skeleton.ι X n le_rfl (y, toTop.map (SimplexCategory.σ j) t),
      (skeleton.ι_map X (n + 1) le_rfl n.le_succ (SimplexCategory.σ j) y t).symm⟩
  · obtain ⟨i, u, rfl⟩ := Set.mem_iUnion.mp (SimplexCategory.toTopBoundary_eq_iUnion_range_δ n ▸ ht)
    exact ⟨skeleton.ι X n le_rfl (X.δ i x, u),
      skeleton.ι_map X (n + 1) n.le_succ le_rfl (SimplexCategory.δ i) x u⟩

private def attachFun (n : ℕ) (a : attachingSet X (n + 1)) : (skeleton X).obj n :=
  (mem_range_succ_of_mem_attachingSet X a.2).choose

private theorem attachFun_spec {n : ℕ} (a : attachingSet X (n + 1)) :
    (skeleton X).map (homOfLE n.le_succ) (attachFun X n a) = skeleton.ι X (n + 1) le_rfl a.1 :=
  (mem_range_succ_of_mem_attachingSet X a.2).choose_spec

private theorem attachFun_map_left {n k : ℕ} (hk : k ≤ n) (f : ⦋n + 1⦌ ⟶ ⦋k⦌) (y : X _⦋k⦌)
    (t : toTop.{u}.obj ⦋n + 1⦌) (h : (X.map f.op y, t) ∈ attachingSet X (n + 1)) :
    attachFun X n ⟨(X.map f.op y, t), h⟩ = skeleton.ι X n hk (y, toTop.map f t) :=
  skeleton_map_injective X n.le_succ <| (attachFun_spec X _).trans
    (skeleton.ι_map X (n + 1) le_rfl (hk.trans n.le_succ) f y t)

private theorem attachFun_map_right {n l : ℕ} (hl : l ≤ n) (f : ⦋l⦌ ⟶ ⦋n + 1⦌) (x : X _⦋n + 1⦌)
    (u : toTop.{u}.obj ⦋l⦌) (h : (x, toTop.map f u) ∈ attachingSet X (n + 1)) :
    attachFun X n ⟨(x, toTop.map f u), h⟩ = skeleton.ι X n hl (X.map f.op x, u) :=
  skeleton_map_injective X n.le_succ <| (attachFun_spec X _).trans
    (skeleton.ι_map X (n + 1) (hl.trans n.le_succ) le_rfl f x u).symm

private theorem image_val_preimage_attachFun {n : ℕ} (F : Set ((skeleton X).obj n)) :
    Subtype.val '' (attachFun X n ⁻¹' F) =
      (⋃ j : Fin (n + 1), Prod.map (X.σ j) id ''
        ((fun p : X _⦋n⦌ × toTop.{u}.obj ⦋n + 1⦌ ↦
          skeleton.ι X n le_rfl (p.1, toTop.map (SimplexCategory.σ j) p.2)) ⁻¹' F)) ∪
      (⋃ i : Fin (n + 2), Prod.map id (toTop.map (SimplexCategory.δ i)) ''
        ((fun p : X _⦋n + 1⦌ × toTop.{u}.obj ⦋n⦌ ↦
          skeleton.ι X n le_rfl (X.δ i p.1, p.2)) ⁻¹' F)) := by
  ext p; constructor
  · rintro ⟨⟨⟨x, t⟩, hmem⟩, hF, rfl⟩
    have hmem' := hmem; rcases hmem' with ⟨hx, -⟩ | ⟨-, ht⟩
    · obtain ⟨j, y, rfl⟩ :=
        Set.mem_iUnion.mp (SSet.degenerate_eq_iUnion_range_σ (X ⋙ forget TopCat) ▸ hx)
      exact Or.inl <| Set.mem_iUnion.mpr ⟨j, (y, t),
        (congrArg (· ∈ F) (attachFun_map_left X le_rfl (SimplexCategory.σ j) y t hmem)).mp hF,
        rfl⟩
    · obtain ⟨i, u, rfl⟩ :=
        Set.mem_iUnion.mp (SimplexCategory.toTopBoundary_eq_iUnion_range_δ n ▸ ht)
      exact Or.inr <| Set.mem_iUnion.mpr ⟨i, (x, u),
        (congrArg (· ∈ F) (attachFun_map_right X le_rfl (SimplexCategory.δ i) x u hmem)).mp hF,
        rfl⟩
  · rintro (hσ | hδ)
    · obtain ⟨j, ⟨y, t⟩, hy, rfl⟩ := Set.mem_iUnion.mp hσ
      have hmem : (X.σ j y, t) ∈ attachingSet X (n + 1) :=
        Or.inl ⟨SSet.σ_mem_degenerate (X := X ⋙ forget TopCat) j y, trivial⟩
      exact ⟨⟨(X.σ j y, t), hmem⟩,
        (congrArg (· ∈ F) (attachFun_map_left X le_rfl (SimplexCategory.σ j) y t hmem)).mpr hy,
        rfl⟩
    · obtain ⟨i, ⟨x, u⟩, hx, rfl⟩ := Set.mem_iUnion.mp hδ
      have hmem : (x, toTop.map (SimplexCategory.δ i) u) ∈ attachingSet X (n + 1) :=
        Or.inr ⟨trivial,
          SimplexCategory.toTop_map_mem_toTopBoundary_of_len_lt (SimplexCategory.δ i) (by simp) u⟩
      exact ⟨⟨(x, toTop.map (SimplexCategory.δ i) u), hmem⟩,
        (congrArg (· ∈ F) (attachFun_map_right X le_rfl (SimplexCategory.δ i) x u hmem)).mpr hx,
        rfl⟩

private theorem continuous_attachFun {n : ℕ}
    (hσ : ∀ j : Fin (n + 1), IsClosedEmbedding (X.σ j)) : Continuous (attachFun X n) := by
  rw [continuous_iff_isClosed]; intro F hF
  rw [← Set.preimage_image_eq (attachFun X n ⁻¹' F) Subtype.val_injective]
  refine IsClosed.preimage continuous_subtype_val ?_
  rw [image_val_preimage_attachFun]
  refine (isClosed_iUnion_of_finite fun j ↦ ?_).union (isClosed_iUnion_of_finite fun i ↦ ?_)
  · exact ((hσ j).prodMap .id).isClosedMap _ (hF.preimage <| (skeleton.ι X n le_rfl).continuous.comp
      <| continuous_fst.prodMk
        ((toTop.map (SimplexCategory.σ j)).hom.continuous.comp continuous_snd))
  · exact (IsClosedEmbedding.id.prodMap
      (SimplexCategory.isClosedEmbedding_toTop_map_of_mono (SimplexCategory.δ i))).isClosedMap _
      (hF.preimage <| (skeleton.ι X n le_rfl).continuous.comp
        (((X.δ i).hom.continuous.comp continuous_fst).prodMk continuous_snd))

/-- The continuous attaching map `attachingSet X (n + 1) ⟶ skₙ |X|` when all degeneracies in
degree `n` are closed embeddings. -/
def attachMap (n : ℕ) (hσ : ∀ j : Fin (n + 1), IsClosedEmbedding (X.σ j)) :
    TopCat.of (attachingSet X (n + 1)) ⟶ (skeleton X).obj n :=
  TopCat.ofHom ⟨attachFun X n, continuous_attachFun X hσ⟩

private theorem pushout_rel_le_succ {n l : ℕ} {Z : TopCat.{u}} (hl : l ≤ n)
    (f : ⦋l⦌ ⟶ ⦋n + 1⦌) (x : X _⦋n + 1⦌) (u : toTop.{u}.obj ⦋l⦌)
    {hσ : ∀ j : Fin (n + 1), IsClosedEmbedding (X.σ j)} {inl : (skeleton X).obj n ⟶ Z}
    {inr : TopCat.of (X _⦋n + 1⦌ × toTop.{u}.obj ⦋n + 1⦌) ⟶ Z}
    (hw : attachMap X n hσ ≫ inl = TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ ≫ inr) :
    inl (skeleton.ι X n hl (X.map f.op x, u)) = inr (x, toTop.map f u) := by
  have hmem : (x, toTop.map f u) ∈ attachingSet X (n + 1) := Or.inr ⟨trivial,
    SimplexCategory.toTop_map_mem_toTopBoundary_of_len_lt f (Nat.lt_succ_of_le hl) u⟩
  exact (congrArg inl (attachFun_map_right X hl f x u hmem).symm).trans
    (ConcreteCategory.congr_hom hw ⟨(x, toTop.map f u), hmem⟩)

private theorem pushout_rel_succ_le {n k : ℕ} {Z : TopCat.{u}} (hk : k ≤ n)
    (f : ⦋n + 1⦌ ⟶ ⦋k⦌) (x : X _⦋k⦌) (u : toTop.{u}.obj ⦋n + 1⦌)
    {hσ : ∀ j : Fin (n + 1), IsClosedEmbedding (X.σ j)} {inl : (skeleton X).obj n ⟶ Z}
    {inr : TopCat.of (X _⦋n + 1⦌ × toTop.{u}.obj ⦋n + 1⦌) ⟶ Z}
    (hw : attachMap X n hσ ≫ inl = TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ ≫ inr) :
    inr (X.map f.op x, u) = inl (skeleton.ι X n hk (x, toTop.map f u)) := by
  have hmem : (X.map f.op x, u) ∈ attachingSet X (n + 1) :=
    Or.inl ⟨⟨k, Nat.lt_succ_of_le hk, f, x, rfl⟩, trivial⟩
  exact (ConcreteCategory.congr_hom hw ⟨(X.map f.op x, u), hmem⟩).symm.trans
    (congrArg inl (attachFun_map_left X hk f x u hmem))

private theorem pushout_rel_succ_succ {n : ℕ} {Z : TopCat.{u}}
    (f : ⦋n + 1⦌ ⟶ ⦋n + 1⦌) (x : X _⦋n + 1⦌) (u : toTop.{u}.obj ⦋n + 1⦌)
    {hσ : ∀ j : Fin (n + 1), IsClosedEmbedding (X.σ j)} {inl : (skeleton X).obj n ⟶ Z}
    {inr : TopCat.of (X _⦋n + 1⦌ × toTop.{u}.obj ⦋n + 1⦌) ⟶ Z}
    (hw : attachMap X n hσ ≫ inl = TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ ≫ inr) :
    inr (X.map f.op x, u) = inr (x, toTop.map f u) := by
  by_cases hiso : IsIso f
  · obtain rfl := SimplexCategory.eq_id_of_isIso f
    rw [op_id, X.map_id, toTop.map_id, TopCat.id_app, TopCat.id_app]
  · let r := (Limits.image f).len
    have hr : r ≤ n := by
      have hle : r ≤ n + 1 := SimplexCategory.le_of_mono (Limits.image.ι f)
      by_contra hgt
      have hlen : r = n + 1 := by omega
      have := (SimplexCategory.isIso_iff_of_mono (Limits.image.ι f)).mpr hlen
      have := (SimplexCategory.isIso_iff_of_epi (Limits.factorThruImage f)).mpr hlen.symm
      exact hiso (Limits.image.fac f ▸ inferInstance)
    calc inr (X.map f.op x, u)
      _ = inr (X.map (Limits.factorThruImage f).op (X.map (Limits.image.ι f).op x), u) := by
          rw [← TopCat.comp_app, ← X.map_comp, ← op_comp, Limits.image.fac f]
      _ = inl (skeleton.ι X n hr
            (X.map (Limits.image.ι f).op x, toTop.map (Limits.factorThruImage f) u)) :=
          pushout_rel_succ_le X hr (Limits.factorThruImage f) _ u hw
      _ = inr (x, toTop.map f u) := by
          rw [pushout_rel_le_succ X hr (Limits.image.ι f) x _ hw, ← TopCat.comp_app,
            ← toTop.map_comp, Limits.image.fac f]

private def skeletonSuccRaw {n : ℕ} {Z : TopCat.{u}} (inl : (skeleton X).obj n ⟶ Z)
    (inr : TopCat.of (X _⦋n + 1⦌ × toTop.{u}.obj ⦋n + 1⦌) ⟶ Z)
    (p : Σ k : {k : ℕ // k ≤ n + 1}, X _⦋k.1⦌ × toTop.{u}.obj ⦋k.1⦌) : Z :=
  if h : p.1.1 ≤ n then inl (skeleton.ι X n h p.2)
  else inr ((by have := p.1.2; omega : p.1.1 = n + 1) ▸ p.2)

private def skeletonSuccDesc {n : ℕ} {Z : TopCat.{u}}
    {hσ : ∀ j : Fin (n + 1), IsClosedEmbedding (X.σ j)} (inl : (skeleton X).obj n ⟶ Z)
    (inr : TopCat.of (X _⦋n + 1⦌ × toTop.{u}.obj ⦋n + 1⦌) ⟶ Z)
    (hw : attachMap X n hσ ≫ inl = TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ ≫ inr) :
    (skeleton X).obj (n + 1) ⟶ Z :=
  TopCat.ofHom
    { toFun := Quot.lift (skeletonSuccRaw X inl inr) <| by
        intro _ _ hrel; cases hrel with
        | @mk l k hl hk f x u =>
          by_cases hl' : l ≤ n <;> by_cases hk' : k ≤ n
          · simp [skeletonSuccRaw, hl', hk', skeleton.ι_map X n hl' hk' f x u]
          · obtain rfl : k = n + 1 := by omega
            simpa [skeletonSuccRaw, hl', hk'] using pushout_rel_le_succ X hl' f x u hw
          · obtain rfl : l = n + 1 := by omega
            simpa [skeletonSuccRaw, hl', hk'] using pushout_rel_succ_le X hk' f x u hw
          · obtain rfl : l = n + 1 := by omega
            obtain rfl : k = n + 1 := by omega
            simpa [skeletonSuccRaw, hl'] using pushout_rel_succ_succ X f x u hw
      continuous_toFun := continuous_quot_lift _ <| continuous_sigma fun ⟨k, hk⟩ ↦ by
        by_cases h : k ≤ n
        · exact (inl.hom.continuous.comp (skeleton.ι X n h).continuous).congr
            fun p ↦ by simp [skeletonSuccRaw, h]; rfl
        · obtain rfl : k = n + 1 := by omega
          exact inr.hom.continuous.congr fun p ↦ by simp [skeletonSuccRaw, h] }

/-- **Skeletal pushout theorem.** When all degeneracies `X.σ j` in degree `n` are closed embeddings,
stage `n + 1` of the skeletal filtration is the pushout in `TopCat` of stage `n` and
`X _⦋n + 1⦌ × Δⁿ⁺¹` along the closed attaching subspace `attachingSet X (n + 1)`. -/
theorem isPushout_skeleton_succ (n : ℕ) (hσ : ∀ j : Fin (n + 1), IsClosedEmbedding (X.σ j)) :
    IsPushout (attachMap X n hσ) (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
      ((skeleton X).map (homOfLE n.le_succ)) (skeleton.ιHom X (n + 1) le_rfl) := by
  have w : attachMap X n hσ ≫ (skeleton X).map (homOfLE n.le_succ) =
      TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ ≫ skeleton.ιHom X (n + 1) le_rfl := by
    ext a; exact attachFun_spec X a
  refine IsPushout.of_isColimit' ⟨w⟩ (PushoutCocone.IsColimit.mk w
    (fun s ↦ skeletonSuccDesc X s.inl s.inr s.condition)
    (fun s ↦ skeleton.hom_ext X fun k hk x t ↦ by
      change skeletonSuccRaw X s.inl s.inr ⟨⟨k, hk.trans n.le_succ⟩, x, t⟩ =
        s.inl (skeleton.ι X n hk (x, t))
      simp [skeletonSuccRaw, hk])
    (fun s ↦ by
      ext ⟨x, t⟩
      change skeletonSuccRaw X s.inl s.inr ⟨⟨n + 1, le_rfl⟩, x, t⟩ = s.inr (x, t)
      have hn : ¬ n + 1 ≤ n := by omega
      simp [skeletonSuccRaw, hn])
    fun s m hinl hinr ↦ skeleton.hom_ext X fun k hk x t ↦ ?_)
  by_cases hk' : k ≤ n
  · refine (ConcreteCategory.congr_hom hinl (skeleton.ι X n hk' (x, t))).trans ?_
    change s.inl (skeleton.ι X n hk' (x, t)) = skeletonSuccRaw X s.inl s.inr ⟨⟨k, hk⟩, x, t⟩
    simp [skeletonSuccRaw, hk']
  · obtain rfl : k = n + 1 := by omega
    refine (ConcreteCategory.congr_hom hinr (x, t)).trans ?_
    change s.inr (x, t) = skeletonSuccRaw X s.inl s.inr ⟨⟨n + 1, hk⟩, x, t⟩
    simp [skeletonSuccRaw, hk']

end Pushout

section Topology

private theorem preimage_ι_singleton_eq_iUnion (p : X.geometricRealization) (n : ℕ) :
    ι X n ⁻¹' {p} =
      ⋃ (m : Fin (n + 1)) (μ : ⦋m.1⦌ ⟶ ⦋n⦌) (_ : Mono μ) (π : ⦋m.1⦌ ⟶ ⦋(normalForm X p).dim⦌),
        {x | X.map μ.op x = X.map π.op (normalForm X p).simplex.1} ×ˢ
          (toTop.map μ '' (toTop.map π ⁻¹' {(normalForm X p).point.1})) := by
  ext ⟨x, t⟩; simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff]; constructor
  · intro hp
    rcases hp ▸ isNormalForm_normalForm_ι X x t with ⟨k, μ, hμ, u, _, π, _, ht, hx, hp'⟩
    exact ⟨⟨k, Nat.lt_succ_of_le (SimplexCategory.le_of_mono μ)⟩, μ, hμ, π, hx, u, hp', ht⟩
  · rintro ⟨m, μ, _, π, hx, u, hu, rfl⟩
    rw [← ι_map, show X.map μ.op x = _ from hx, ι_map, show toTop.map π u = _ from hu]
    exact toRealization_normalForm X p

/-- If each level `X _⦋n⦌` is `T1`, then `|X|` is `T1` in its colimit topology. -/
instance instT1Space [∀ n : ℕ, T1Space (X _⦋n⦌)] : T1Space X.geometricRealization := by
  refine ⟨fun p ↦ (isClosed_iff X).mpr fun n ↦ ?_⟩
  rw [preimage_ι_singleton_eq_iUnion X p n]
  refine isClosed_iUnion_of_finite fun m ↦ isClosed_iUnion_of_finite fun μ ↦
    isClosed_iUnion_of_finite fun _ ↦ isClosed_iUnion_of_finite fun π ↦ ?_
  exact (isClosed_singleton.preimage (X.map μ.op).hom.continuous).prod <|
    (SimplexCategory.isClosedEmbedding_toTop_map_of_mono μ).isClosedMap _
      (isClosed_singleton.preimage (toTop.map π).hom.continuous)

/-- If each level `X _⦋k⦌` is `T1`, every stage `skₙ |X|` of the skeletal filtration is `T1`. -/
instance instT1SpaceSkeleton [∀ k : ℕ, T1Space (X _⦋k⦌)] (n : ℕ) :
    T1Space ((skeleton X).obj n) :=
  ⟨fun q ↦ by
    rw [← Set.preimage_image_eq {q} (skeleton.toRealization_injective X n), Set.image_singleton]
    exact isClosed_singleton.preimage (skeleton.toRealization X n).hom.continuous⟩

/-- Every compact subset of `|X|` lies in a single skeleton `skₙ |X|` whenever each `X _⦋n⦌` is
`T1`, with no hypothesis on degeneracies. -/
theorem exists_subset_range_skeleton_toRealization_of_isCompact [∀ n : ℕ, T1Space (X _⦋n⦌)]
    {K : Set X.geometricRealization} (hK : IsCompact K) :
    ∃ n : ℕ, K ⊆ Set.range (skeleton.toRealization X n) :=
  TauCeti.TopCat.exists_subset_range_ι_of_isCompact
    (fun _ _ hij ↦ skeleton_map_injective X hij) (isColimitSkeletonCocone X) hK

private theorem isClosed_degenerate_succ {n : ℕ}
    (hσ : ∀ j : Fin (n + 1), IsClosedEmbedding (X.σ j)) :
    IsClosed (X := X _⦋n + 1⦌) (SSet.degenerate (X ⋙ forget TopCat) (n + 1)) := by
  rw [SSet.degenerate_eq_iUnion_range_σ]
  exact isClosed_iUnion_of_finite fun j ↦ (hσ j).isClosed_range

/-- If all degeneracies in degree `n` are closed embeddings, `skₙ |X| ⟶ skₙ₊₁ |X|` is a closed
embedding. -/
theorem isClosedEmbedding_skeleton_succ {n : ℕ}
    (hσ : ∀ j : Fin (n + 1), IsClosedEmbedding (X.σ j)) :
    IsClosedEmbedding ((skeleton X).map (homOfLE n.le_succ)) :=
  TauCeti.TopCat.isClosedEmbedding_of_isPushout (isPushout_skeleton_succ X n hσ)
    (isClosed_attachingSet X (isClosed_degenerate_succ X hσ)).isClosedEmbedding_subtypeVal

section ClosedDegeneracies

variable (hσ : ∀ {n : ℕ} (j : Fin (n + 1)), IsClosedEmbedding (X.σ j))
include hσ

/-- If all degeneracies of `X` are closed embeddings, every skeletal transition map is a closed
embedding. -/
theorem isClosedEmbedding_skeleton_map {m n : ℕ} (hmn : m ≤ n) :
    IsClosedEmbedding ((skeleton X).map (homOfLE hmn)) :=
  TauCeti.TopCat.isClosedEmbedding_map_of_isWellOrderContinuous (skeleton X)
    (fun _ _ ↦ isClosedEmbedding_skeleton_succ X hσ) hmn

/-- If all degeneracies of `X` are closed embeddings, every stage inclusion `skₙ |X| ⟶ |X|` is a
closed embedding. -/
theorem isClosedEmbedding_skeleton_toRealization (n : ℕ) :
    IsClosedEmbedding (skeleton.toRealization X n) :=
  TauCeti.TopCat.isClosedEmbedding_ι_of_isColimit_of_succ
    (fun _ ↦ isClosedEmbedding_skeleton_succ X hσ) (isColimitSkeletonCocone X) n

/-- Every continuous map from a compact space into `|X|` factors continuously through a single
skeleton `skₙ |X|` when each `X _⦋n⦌` is `T1` and all degeneracies are closed embeddings. -/
theorem exists_lift_skeleton_of_compactSpace [∀ n : ℕ, T1Space (X _⦋n⦌)]
    {K : Type*} [TopologicalSpace K] [CompactSpace K] (g : C(K, X.geometricRealization)) :
    ∃ (n : ℕ) (g' : C(K, (skeleton X).obj n)), (skeleton.toRealization X n).hom.comp g' = g :=
  TauCeti.TopCat.exists_lift_of_compactSpace (isColimitSkeletonCocone X)
    (fun n ↦ (isClosedEmbedding_skeleton_toRealization X hσ n).isEmbedding) g

/-- If each `X _⦋n⦌ × Δⁿ` is normal and all degeneracies are closed embeddings, every stage
`skₙ |X|` is normal. -/
theorem normalSpace_skeleton [∀ n : ℕ, NormalSpace (X _⦋n⦌ × toTop.{u}.obj ⦋n⦌)] (n : ℕ) :
    NormalSpace ((skeleton X).obj n) := by
  induction n with
  | zero =>
    have := (Homeomorph.prodUnique (X _⦋0⦌) (toTop.{u}.obj ⦋0⦌)).normalSpace
    exact (TopCat.homeoOfIso (skeletonZeroIso X)).symm.normalSpace
  | succ n _ =>
    exact TauCeti.TopCat.normalSpace_of_isPushout (isPushout_skeleton_succ X n hσ)
      (isClosed_attachingSet X (isClosed_degenerate_succ X hσ)).isClosedEmbedding_subtypeVal

/-- If each `X _⦋n⦌ × Δⁿ` is normal and all degeneracies are closed embeddings, `|X|` is normal in
its colimit topology. -/
theorem normalSpace [∀ n : ℕ, NormalSpace (X _⦋n⦌ × toTop.{u}.obj ⦋n⦌)] :
    NormalSpace X.geometricRealization := by
  have := normalSpace_skeleton X hσ
  exact TauCeti.TopCat.normalSpace_of_isColimit
    (fun n ↦ isClosedEmbedding_skeleton_succ X hσ) (isColimitSkeletonCocone X)

end ClosedDegeneracies

/-- **Separation of thin geometric realization.** If each `X _⦋n⦌` is `T1` and each `X _⦋n⦌ × Δⁿ` is
normal, `|X|` is `T4` — and hence Hausdorff, and paracompact whenever each `X _⦋n⦌ × Δⁿ` is
Lindelöf — in its actual colimit topology. -/
instance instT4Space [∀ n : ℕ, T1Space (X _⦋n⦌)]
    [∀ n : ℕ, NormalSpace (X _⦋n⦌ × toTop.{u}.obj ⦋n⦌)] : T4Space X.geometricRealization := by
  have : NormalSpace X.geometricRealization := normalSpace X fun {n} j ↦ by
    have : T4Space (X _⦋n + 1⦌ × toTop.{u}.obj ⦋n + 1⦌) := {}
    have : T2Space (X _⦋n + 1⦌) :=
      (IsEmbedding.of_leftInverse (f := fun p : X _⦋n + 1⦌ × toTop.{u}.obj ⦋n + 1⦌ ↦ p.1)
        (g := fun x ↦ (x, SimplexCategory.toTopInitialVertex.{u} ⦋n + 1⦌))
        (fun _ ↦ rfl) continuous_fst (continuous_id.prodMk continuous_const)).t2Space
    exact X.isClosedEmbedding_σ j
  exact {}

end Topology

end CategoryTheory.SimplicialObject.geometricRealization
