/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocallyConstant.Algebra
public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Stratum
public import TauCeti.Topology.VectorBundle.FiniteRank.Biproduct

/-!
# Variable-rank trivial atlases and Whitney biproducts

Given a locally constant rank function `r : LocallyConstant X ℕ`, `FiniteRankAtlas.trivial 𝕜 X r`
places the standard trivial core of rank `n` on each clopen stratum `{x : X // r x = n}`. Its
rank-zero specialization `trivial 𝕜 X 0` is a zero object (`HasZeroObject (FiniteRankAtlas 𝕜 X)`).

Given two variable-rank bundle atlases `A` and `D`, `FiniteRankAtlas.whitneySum A D` glues the
constant-rank Whitney sums of their restrictions to the joint clopen rank bi-strata
`{x : X // (A.rank x, D.rank x) = p}` via `FiniteRankAtlas.ofClopenCores`. Because several input
rank pairs `(m, n)` merge into the same output stratum `m + n`, this requires the clopen-partition
gluing infrastructure rather than stratumwise products.

* `whitneyFst`, `whitneySnd`, `whitneyInl`, and `whitneyInr` assemble the block-coordinate
  projections and inclusions across the joint rank bi-strata without completeness assumptions on
  `𝕜`, forming a `BinaryBicone` with `whitney_total` and `whitneyBiconeIsBilimit`.
* `HasBinaryBiproducts (FiniteRankAtlas 𝕜 X)` equips `FiniteRankAtlas 𝕜 X` with binary biproducts,
  with `@[simp]` rank formulas `rank_zero` and `rank_biprod`.
* `ofCoreWhitneySumIso` shows that the constant-rank embedding `ofCore` preserves concrete Whitney
  sums up to canonical isomorphism intertwining the four bicone legs.
* `whitneySumFiberProdHomeomorph` identifies the reconstructed total space of `whitneySum A D` over
  `X` with the topological fibre product
  `{pq : TotalSpace Unit A.Fiber × TotalSpace Unit D.Fiber // pq.1.proj = pq.2.proj}`.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.1.
* M. F. Atiyah, *K-Theory*, §1.1–1.2.
-/

public section

open Bundle CategoryTheory CategoryTheory.Limits Topology VectorBundleCore
open scoped ZeroObject

namespace TauCeti.FiniteRankAtlas

universe u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {X : Type u} [TopologicalSpace X]

/-! ### Variable-rank trivial atlases and zero object -/

section Trivial

variable (𝕜 X) in
/-- The trivial variable-rank bundle atlas of locally constant rank `r`, with a single global
coordinate chart on each clopen rank stratum. -/
-- Expose the rank projection so fibre types over `x` reduce to `Fin (r x) → 𝕜`.
@[expose, implicit_reducible]
def trivial (r : LocallyConstant X ℕ) : FiniteRankAtlas 𝕜 X where
  rank := r
  charts n := (FiniteRankBundleCore.trivial 𝕜 {x : X // r x = n} n).core
  indexAt_eq _ _ := rfl

@[simp]
theorem rank_trivial (r : LocallyConstant X ℕ) :
    (trivial 𝕜 X r).rank = r :=
  (rfl)

@[simp]
theorem stratumCore_trivial (r : LocallyConstant X ℕ) (n : ℕ) :
    (trivial 𝕜 X r).stratumCore n = FiniteRankBundleCore.trivial 𝕜 {x : X // r x = n} n :=
  (rfl)

@[simp]
theorem toCore_trivial (n : ℕ) :
    (trivial 𝕜 X (LocallyConstant.const X n)).toCore n (fun _ ↦ rfl) =
      FiniteRankBundleCore.trivial 𝕜 X n :=
  (rfl)

/-- A constant-rank trivial core embeds via `ofCore` as the constant-rank trivial atlas. -/
noncomputable def ofCoreTrivialIso (n : ℕ) :
    ofCore.obj (FiniteRankBundleCore.trivial 𝕜 X n) ≅
      trivial 𝕜 X (LocallyConstant.const X n) :=
  (trivial 𝕜 X (LocallyConstant.const X n)).ofCoreToCoreIso n (fun _ ↦ rfl)

@[simp]
theorem fiberMap_ofCoreTrivialIso_hom (n : ℕ) (x : X) :
    (ofCoreTrivialIso (𝕜 := 𝕜) (X := X) n).hom.fiberMap x = LinearMap.id := by
  apply LinearMap.ext
  intro v
  exact (trivial 𝕜 X (LocallyConstant.const X n)).fiberMap_ofCoreToCoreIso_hom n (fun _ ↦ rfl) x v

@[simp]
theorem fiberMap_ofCoreTrivialIso_inv (n : ℕ) (x : X) :
    (ofCoreTrivialIso (𝕜 := 𝕜) (X := X) n).inv.fiberMap x = LinearMap.id := by
  apply LinearMap.ext
  intro v
  exact (trivial 𝕜 X (LocallyConstant.const X n)).fiberMap_ofCoreToCoreIso_inv n (fun _ ↦ rfl) x v

/-- A map into the reconstructed total space of `trivial 𝕜 X r` over a continuous base map `b` is
continuous if and only if its coordinate vector is continuous on every clopen rank stratum. -/
theorem continuous_mk_trivial_iff {Y : Type*} [TopologicalSpace Y] {b : Y → X}
    (hb : Continuous b) (r : LocallyConstant X ℕ) (s : ∀ y, (trivial 𝕜 X r).Fiber (b y)) :
    Continuous (fun y ↦ (⟨b y, s y⟩ : TotalSpace Unit (trivial 𝕜 X r).Fiber)) ↔
      ∀ n : ℕ, Continuous (fun y : {y : Y // r (b y) = n} ↦
        (fun i : Fin n ↦ s y.1 (Fin.cast y.2.symm i))) := by
  rw [(trivial 𝕜 X r).continuous_mk_iff_rankStrata hb s]
  refine forall_congr' fun n ↦ ?_
  exact FiniteRankBundleCore.continuous_trivial_iff.trans
    (and_iff_right ((hb.comp continuous_subtype_val).subtype_mk _))

/-- Any variable-rank atlas whose rank is identically zero is a zero object. -/
theorem isZero_of_rank_eq_zero (A : FiniteRankAtlas 𝕜 X) (h : A.rank = 0) : IsZero A where
  unique_to D := ⟨⟨⟨0⟩, fun f ↦ by
    apply hom_ext
    intro x
    apply LinearMap.ext
    intro v
    have hx : A.rank x = 0 := by rw [h]; rfl
    have : Subsingleton (A.Fiber x) := by
      -- Unfold `A.Fiber x` to `Fin (A.rank x) → 𝕜` so `hx` rewrites the domain to `Fin 0`.
      change Subsingleton (Fin (A.rank x) → 𝕜)
      rw [hx]
      infer_instance
    rw [Subsingleton.elim v 0, map_zero, map_zero]⟩⟩
  unique_from D := ⟨⟨⟨0⟩, fun f ↦ by
    apply hom_ext
    intro x
    apply LinearMap.ext
    intro v
    ext i
    have hx : A.rank x = 0 := by rw [h]; rfl
    exact (Fin.cast hx i).elim0⟩⟩

/-- The trivial rank-zero atlas is a zero object in `FiniteRankAtlas 𝕜 X`. -/
theorem isZero_trivial_zero : IsZero (trivial 𝕜 X 0) :=
  isZero_of_rank_eq_zero _ rfl

instance : HasZeroObject (FiniteRankAtlas 𝕜 X) :=
  ⟨⟨trivial 𝕜 X 0, isZero_trivial_zero⟩⟩

@[simp]
theorem rank_zero : (0 : FiniteRankAtlas 𝕜 X).rank = 0 :=
  ((Limits.isZero_zero (FiniteRankAtlas 𝕜 X)).iso isZero_trivial_zero).finiteRankAtlas_rank_eq

end Trivial

/-! ### Variable-rank Whitney sums and binary biproducts -/

/-- The Whitney sum of two variable-rank bundle atlases, assembled over the joint clopen rank
bi-strata `{x : X // (A.rank x, D.rank x) = p}` from constant-rank Whitney sums. -/
-- Expose the glued construction so homs and fibre types reduce over `ofClopenCores`.
@[expose, implicit_reducible]
noncomputable def whitneySum (A D : FiniteRankAtlas 𝕜 X) : FiniteRankAtlas 𝕜 X :=
  ofClopenCores (A.rank.prodMk D.rank) fun p ↦
    (A.clopenPullCore (A.rank.prodMk D.rank) Prod.fst (fun _ ↦ rfl) p).whitneySum
      (D.clopenPullCore (A.rank.prodMk D.rank) Prod.snd (fun _ ↦ rfl) p)

@[simp]
theorem rank_whitneySum (A D : FiniteRankAtlas 𝕜 X) :
    (whitneySum A D).rank = A.rank + D.rank :=
  LocallyConstant.ext fun _ ↦ rfl

/-- Projection of the variable-rank Whitney sum onto its first summand. -/
noncomputable def whitneyFst (A D : FiniteRankAtlas 𝕜 X) : whitneySum A D ⟶ A :=
  mapClopenCores (A.rank.prodMk D.rank) (fun p ↦
    FiniteRankBundleCore.whitneyFst
      (A.clopenPullCore (A.rank.prodMk D.rank) Prod.fst (fun _ ↦ rfl) p)
      (D.clopenPullCore (A.rank.prodMk D.rank) Prod.snd (fun _ ↦ rfl) p)) ≫
    (A.clopenPullIso (A.rank.prodMk D.rank) Prod.fst (fun _ ↦ rfl)).hom

/-- Projection of the variable-rank Whitney sum onto its second summand. -/
noncomputable def whitneySnd (A D : FiniteRankAtlas 𝕜 X) : whitneySum A D ⟶ D :=
  mapClopenCores (A.rank.prodMk D.rank) (fun p ↦
    FiniteRankBundleCore.whitneySnd
      (A.clopenPullCore (A.rank.prodMk D.rank) Prod.fst (fun _ ↦ rfl) p)
      (D.clopenPullCore (A.rank.prodMk D.rank) Prod.snd (fun _ ↦ rfl) p)) ≫
    (D.clopenPullIso (A.rank.prodMk D.rank) Prod.snd (fun _ ↦ rfl)).hom

/-- Inclusion of the first summand into the variable-rank Whitney sum. -/
noncomputable def whitneyInl (A D : FiniteRankAtlas 𝕜 X) : A ⟶ whitneySum A D :=
  (A.clopenPullIso (A.rank.prodMk D.rank) Prod.fst (fun _ ↦ rfl)).inv ≫
    mapClopenCores (A.rank.prodMk D.rank) (fun p ↦
      FiniteRankBundleCore.whitneyInl
        (A.clopenPullCore (A.rank.prodMk D.rank) Prod.fst (fun _ ↦ rfl) p)
        (D.clopenPullCore (A.rank.prodMk D.rank) Prod.snd (fun _ ↦ rfl) p))

/-- Inclusion of the second summand into the variable-rank Whitney sum. -/
noncomputable def whitneyInr (A D : FiniteRankAtlas 𝕜 X) : D ⟶ whitneySum A D :=
  (D.clopenPullIso (A.rank.prodMk D.rank) Prod.snd (fun _ ↦ rfl)).inv ≫
    mapClopenCores (A.rank.prodMk D.rank) (fun p ↦
      FiniteRankBundleCore.whitneyInr
        (A.clopenPullCore (A.rank.prodMk D.rank) Prod.fst (fun _ ↦ rfl) p)
        (D.clopenPullCore (A.rank.prodMk D.rank) Prod.snd (fun _ ↦ rfl) p))

@[simp]
theorem fiberMap_whitneyFst (A D : FiniteRankAtlas 𝕜 X) (x : X)
    (v : (whitneySum A D).Fiber x) :
    (whitneyFst A D).fiberMap x v =
      (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x) v).1 := by
  rw [whitneyFst, fiberMap_comp, LinearMap.comp_apply, fiberMap_clopenPullIso_hom,
    fiberMap_mapClopenCores, FiniteRankBundleCore.fiberMap_whitneyFst]
  rfl

@[simp]
theorem fiberMap_whitneySnd (A D : FiniteRankAtlas 𝕜 X) (x : X)
    (v : (whitneySum A D).Fiber x) :
    (whitneySnd A D).fiberMap x v =
      (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x) v).2 := by
  rw [whitneySnd, fiberMap_comp, LinearMap.comp_apply, fiberMap_clopenPullIso_hom,
    fiberMap_mapClopenCores, FiniteRankBundleCore.fiberMap_whitneySnd]
  rfl

@[simp]
theorem fiberMap_whitneyInl (A D : FiniteRankAtlas 𝕜 X) (x : X) (u : A.Fiber x) :
    (whitneyInl A D).fiberMap x u =
      (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm (u, 0) := by
  rw [whitneyInl, fiberMap_comp, LinearMap.comp_apply, fiberMap_mapClopenCores,
    FiniteRankBundleCore.fiberMap_whitneyInl]
  exact congrArg (fun u' ↦ (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm (u', 0))
    (A.fiberMap_clopenPullIso_inv (A.rank.prodMk D.rank) Prod.fst (fun _ ↦ rfl) x u)

@[simp]
theorem fiberMap_whitneyInr (A D : FiniteRankAtlas 𝕜 X) (x : X) (w : D.Fiber x) :
    (whitneyInr A D).fiberMap x w =
      (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm (0, w) := by
  rw [whitneyInr, fiberMap_comp, LinearMap.comp_apply, fiberMap_mapClopenCores,
    FiniteRankBundleCore.fiberMap_whitneyInr]
  exact congrArg (fun w' ↦ (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm (0, w'))
    (D.fiberMap_clopenPullIso_inv (A.rank.prodMk D.rank) Prod.snd (fun _ ↦ rfl) x w)

@[reassoc (attr := simp)]
theorem whitneyInl_fst (A D : FiniteRankAtlas 𝕜 X) :
    whitneyInl A D ≫ whitneyFst A D = 𝟙 A := by
  dsimp only [whitneyInl, whitneyFst, whitneySum]
  rw [Category.assoc, ← Category.assoc (mapClopenCores _ _), ← mapClopenCores_comp]
  simp

@[reassoc (attr := simp)]
theorem whitneyInl_snd (A D : FiniteRankAtlas 𝕜 X) :
    whitneyInl A D ≫ whitneySnd A D = 0 := by
  dsimp only [whitneyInl, whitneySnd, whitneySum]
  rw [Category.assoc, ← Category.assoc (mapClopenCores _ _), ← mapClopenCores_comp]
  simp

@[reassoc (attr := simp)]
theorem whitneyInr_fst (A D : FiniteRankAtlas 𝕜 X) :
    whitneyInr A D ≫ whitneyFst A D = 0 := by
  dsimp only [whitneyInr, whitneyFst, whitneySum]
  rw [Category.assoc, ← Category.assoc (mapClopenCores _ _), ← mapClopenCores_comp]
  simp

@[reassoc (attr := simp)]
theorem whitneyInr_snd (A D : FiniteRankAtlas 𝕜 X) :
    whitneyInr A D ≫ whitneySnd A D = 𝟙 D := by
  dsimp only [whitneyInr, whitneySnd, whitneySum]
  rw [Category.assoc, ← Category.assoc (mapClopenCores _ _), ← mapClopenCores_comp]
  simp

/-- The variable-rank Whitney sum with its projections and inclusions as a `BinaryBicone`. -/
-- Expose the cone point so leg types reduce to `whitneySum A D`.
@[expose]
noncomputable def whitneyBicone (A D : FiniteRankAtlas 𝕜 X) : BinaryBicone A D where
  pt := whitneySum A D
  fst := whitneyFst A D
  snd := whitneySnd A D
  inl := whitneyInl A D
  inr := whitneyInr A D
  inl_fst := whitneyInl_fst A D
  inl_snd := whitneyInl_snd A D
  inr_fst := whitneyInr_fst A D
  inr_snd := whitneyInr_snd A D

@[simp] theorem whitneyBicone_pt (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyBicone A D).pt = whitneySum A D := (rfl)

@[simp] theorem whitneyBicone_fst (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyBicone A D).fst = whitneyFst A D := (rfl)

@[simp] theorem whitneyBicone_snd (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyBicone A D).snd = whitneySnd A D := (rfl)

@[simp] theorem whitneyBicone_inl (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyBicone A D).inl = whitneyInl A D := (rfl)

@[simp] theorem whitneyBicone_inr (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyBicone A D).inr = whitneyInr A D := (rfl)

/-- The variable-rank Whitney projections and inclusions resolve the identity. -/
@[simp]
theorem whitney_total (A D : FiniteRankAtlas 𝕜 X) :
    whitneyFst A D ≫ whitneyInl A D + whitneySnd A D ≫ whitneyInr A D =
      𝟙 (whitneySum A D) := by
  dsimp only [whitneyFst, whitneyInl, whitneySnd, whitneyInr, whitneySum]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← mapClopenCores_comp]
  rw [← mapClopenCores_add]
  simp only [FiniteRankBundleCore.whitney_total, mapClopenCores_id]

/-- The variable-rank Whitney bicone is a binary bilimit. -/
noncomputable def whitneyBiconeIsBilimit (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyBicone A D).IsBilimit :=
  isBinaryBilimitOfTotal _ (whitney_total A D)

instance : HasBinaryBiproducts (FiniteRankAtlas 𝕜 X) where
  has_binary_biproduct A D := ⟨⟨whitneyBicone A D, whitneyBiconeIsBilimit A D⟩⟩

/-! ### Pairing, copairing, functoriality, and biproduct comparisons -/

section UniversalProperty

variable {A A' A'' D D' C E : FiniteRankAtlas 𝕜 X}

/-- Pair two morphisms into a concrete variable-rank Whitney sum. -/
noncomputable def whitneyLift (f : E ⟶ A) (g : E ⟶ D) : E ⟶ whitneySum A D :=
  f ≫ whitneyInl A D + g ≫ whitneyInr A D

@[reassoc (attr := simp)]
theorem whitneyLift_fst (f : E ⟶ A) (g : E ⟶ D) :
    whitneyLift f g ≫ whitneyFst A D = f := by
  simp [whitneyLift, Preadditive.add_comp]

@[reassoc (attr := simp)]
theorem whitneyLift_snd (f : E ⟶ A) (g : E ⟶ D) :
    whitneyLift f g ≫ whitneySnd A D = g := by
  simp [whitneyLift, Preadditive.add_comp]

/-- Morphisms into `whitneySum A D` are determined by their compositions with the projections. -/
theorem whitneySum_hom_ext {h₁ h₂ : E ⟶ whitneySum A D}
    (hfst : h₁ ≫ whitneyFst A D = h₂ ≫ whitneyFst A D)
    (hsnd : h₁ ≫ whitneySnd A D = h₂ ≫ whitneySnd A D) : h₁ = h₂ :=
  (whitneyBiconeIsBilimit A D).isLimit.hom_ext fun ⟨j⟩ ↦ by cases j <;> assumption

/-- Copair two morphisms out of a concrete variable-rank Whitney sum. -/
noncomputable def whitneyDesc (f : A ⟶ E) (g : D ⟶ E) : whitneySum A D ⟶ E :=
  whitneyFst A D ≫ f + whitneySnd A D ≫ g

@[reassoc (attr := simp)]
theorem whitneyInl_desc (f : A ⟶ E) (g : D ⟶ E) :
    whitneyInl A D ≫ whitneyDesc f g = f := by
  simp [whitneyDesc, Preadditive.comp_add]

@[reassoc (attr := simp)]
theorem whitneyInr_desc (f : A ⟶ E) (g : D ⟶ E) :
    whitneyInr A D ≫ whitneyDesc f g = g := by
  simp [whitneyDesc, Preadditive.comp_add]

@[reassoc (attr := simp)]
theorem whitneyLift_desc (f : E ⟶ A) (g : E ⟶ D) (h : A ⟶ C) (k : D ⟶ C) :
    whitneyLift f g ≫ whitneyDesc h k = f ≫ h + g ≫ k := by
  simp [whitneyLift, whitneyDesc, Preadditive.add_comp, Preadditive.comp_add]

/-- Morphisms out of `whitneySum A D` are determined by their compositions with the inclusions. -/
theorem whitneySum_hom_ext' {h₁ h₂ : whitneySum A D ⟶ E}
    (hinl : whitneyInl A D ≫ h₁ = whitneyInl A D ≫ h₂)
    (hinr : whitneyInr A D ≫ h₁ = whitneyInr A D ≫ h₂) : h₁ = h₂ :=
  (whitneyBiconeIsBilimit A D).isColimit.hom_ext fun ⟨j⟩ ↦ by cases j <;> assumption

/-- Direct sum of two morphisms on concrete variable-rank Whitney sums. -/
noncomputable def whitneyMap (f : A ⟶ A') (g : D ⟶ D') :
    whitneySum A D ⟶ whitneySum A' D' :=
  whitneyLift (whitneyFst A D ≫ f) (whitneySnd A D ≫ g)

@[reassoc (attr := simp)]
theorem whitneyMap_fst (f : A ⟶ A') (g : D ⟶ D') :
    whitneyMap f g ≫ whitneyFst A' D' = whitneyFst A D ≫ f :=
  whitneyLift_fst _ _

@[reassoc (attr := simp)]
theorem whitneyMap_snd (f : A ⟶ A') (g : D ⟶ D') :
    whitneyMap f g ≫ whitneySnd A' D' = whitneySnd A D ≫ g :=
  whitneyLift_snd _ _

@[reassoc (attr := simp)]
theorem whitneyInl_map (f : A ⟶ A') (g : D ⟶ D') :
    whitneyInl A D ≫ whitneyMap f g = f ≫ whitneyInl A' D' :=
  whitneySum_hom_ext (by simp) (by simp)

@[reassoc (attr := simp)]
theorem whitneyInr_map (f : A ⟶ A') (g : D ⟶ D') :
    whitneyInr A D ≫ whitneyMap f g = g ≫ whitneyInr A' D' :=
  whitneySum_hom_ext (by simp) (by simp)

@[simp]
theorem whitneyMap_id (A D : FiniteRankAtlas 𝕜 X) :
    whitneyMap (𝟙 A) (𝟙 D) = 𝟙 (whitneySum A D) :=
  whitneySum_hom_ext (by simp) (by simp)

@[simp]
theorem whitneyMap_comp {D'' : FiniteRankAtlas 𝕜 X}
    (f₁ : A ⟶ A') (f₂ : A' ⟶ A'') (g₁ : D ⟶ D') (g₂ : D' ⟶ D'') :
    whitneyMap (f₁ ≫ f₂) (g₁ ≫ g₂) = whitneyMap f₁ g₁ ≫ whitneyMap f₂ g₂ :=
  whitneySum_hom_ext (by simp) (by simp)

/-- Direct sum of two variable-rank bundle isomorphisms. -/
noncomputable def whitneyMapIso (e₁ : A ≅ A') (e₂ : D ≅ D') :
    whitneySum A D ≅ whitneySum A' D' where
  hom := whitneyMap e₁.hom e₂.hom
  inv := whitneyMap e₁.inv e₂.inv
  hom_inv_id := by rw [← whitneyMap_comp, e₁.hom_inv_id, e₂.hom_inv_id, whitneyMap_id]
  inv_hom_id := by rw [← whitneyMap_comp, e₁.inv_hom_id, e₂.inv_hom_id, whitneyMap_id]

@[simp]
theorem whitneyMapIso_hom (e₁ : A ≅ A') (e₂ : D ≅ D') :
    (whitneyMapIso e₁ e₂).hom = whitneyMap e₁.hom e₂.hom :=
  (rfl)

@[simp]
theorem whitneyMapIso_inv (e₁ : A ≅ A') (e₂ : D ≅ D') :
    (whitneyMapIso e₁ e₂).inv = whitneyMap e₁.inv e₂.inv :=
  (rfl)

end UniversalProperty

/-- Canonical isomorphism between the concrete variable-rank Whitney sum and the categorical binary
biproduct `A ⊞ D`. -/
noncomputable def whitneySumIsoBiprod (A D : FiniteRankAtlas 𝕜 X) :
    whitneySum A D ≅ A ⊞ D where
  hom := biprod.lift (whitneyFst A D) (whitneySnd A D)
  inv := biprod.desc (whitneyInl A D) (whitneyInr A D)
  hom_inv_id := by
    rw [biprod.lift_desc, whitney_total]
  inv_hom_id := by
    apply biprod.hom_ext <;> apply biprod.hom_ext' <;> simp

@[reassoc (attr := simp)]
theorem whitneySumIsoBiprod_hom_fst (A D : FiniteRankAtlas 𝕜 X) :
    (whitneySumIsoBiprod A D).hom ≫ biprod.fst = whitneyFst A D :=
  biprod.lift_fst _ _

@[reassoc (attr := simp)]
theorem whitneySumIsoBiprod_hom_snd (A D : FiniteRankAtlas 𝕜 X) :
    (whitneySumIsoBiprod A D).hom ≫ biprod.snd = whitneySnd A D :=
  biprod.lift_snd _ _

@[reassoc (attr := simp)]
theorem inl_whitneySumIsoBiprod_hom (A D : FiniteRankAtlas 𝕜 X) :
    whitneyInl A D ≫ (whitneySumIsoBiprod A D).hom = biprod.inl := by
  apply biprod.hom_ext <;> simp [whitneySumIsoBiprod]

@[reassoc (attr := simp)]
theorem inr_whitneySumIsoBiprod_hom (A D : FiniteRankAtlas 𝕜 X) :
    whitneyInr A D ≫ (whitneySumIsoBiprod A D).hom = biprod.inr := by
  apply biprod.hom_ext <;> simp [whitneySumIsoBiprod]

@[simp]
theorem rank_biprod (A D : FiniteRankAtlas 𝕜 X) :
    (A ⊞ D).rank = A.rank + D.rank :=
  (whitneySumIsoBiprod A D).symm.finiteRankAtlas_rank_eq.trans (rank_whitneySum A D)

/-- The constant-rank embedding `ofCore` preserves concrete Whitney sums up to canonical
isomorphism intertwining the projections and inclusions. -/
noncomputable def ofCoreWhitneySumIso (B B' : FiniteRankBundleCore 𝕜 X) :
    ofCore.obj (B.whitneySum B') ≅ whitneySum (ofCore.obj B) (ofCore.obj B') where
  hom := whitneyLift (ofCore.map (B.whitneyFst B')) (ofCore.map (B.whitneySnd B'))
  inv := whitneyDesc (ofCore.map (B.whitneyInl B')) (ofCore.map (B.whitneyInr B'))
  hom_inv_id := by
    rw [whitneyLift_desc, ← ofCore.map_comp, ← ofCore.map_comp, ← ofCore.map_add,
      FiniteRankBundleCore.whitney_total, ofCore.map_id]
  inv_hom_id := by
    apply whitneySum_hom_ext
    · apply whitneySum_hom_ext' <;> simp [← ofCore.map_comp]
    · apply whitneySum_hom_ext' <;> simp [← ofCore.map_comp]

@[reassoc (attr := simp)]
theorem ofCoreWhitneySumIso_hom_fst (B B' : FiniteRankBundleCore 𝕜 X) :
    (ofCoreWhitneySumIso B B').hom ≫ whitneyFst (ofCore.obj B) (ofCore.obj B') =
      ofCore.map (B.whitneyFst B') :=
  whitneyLift_fst _ _

@[reassoc (attr := simp)]
theorem ofCoreWhitneySumIso_hom_snd (B B' : FiniteRankBundleCore 𝕜 X) :
    (ofCoreWhitneySumIso B B').hom ≫ whitneySnd (ofCore.obj B) (ofCore.obj B') =
      ofCore.map (B.whitneySnd B') :=
  whitneyLift_snd _ _

@[reassoc (attr := simp)]
theorem inl_ofCoreWhitneySumIso_hom (B B' : FiniteRankBundleCore 𝕜 X) :
    ofCore.map (B.whitneyInl B') ≫ (ofCoreWhitneySumIso B B').hom =
      whitneyInl (ofCore.obj B) (ofCore.obj B') := by
  apply whitneySum_hom_ext <;> simp [← ofCore.map_comp]

@[reassoc (attr := simp)]
theorem inr_ofCoreWhitneySumIso_hom (B B' : FiniteRankBundleCore 𝕜 X) :
    ofCore.map (B.whitneyInr B') ≫ (ofCoreWhitneySumIso B B').hom =
      whitneyInr (ofCore.obj B) (ofCore.obj B') := by
  apply whitneySum_hom_ext <;> simp [← ofCore.map_comp]

/-! ### Total-space fibre-product comparison -/

private noncomputable def whitneyFiberProdEquiv (A D : FiniteRankAtlas 𝕜 X) :
    TotalSpace Unit (whitneySum A D).Fiber ≃
      {pq : TotalSpace Unit A.Fiber × TotalSpace Unit D.Fiber // pq.1.proj = pq.2.proj} where
  toFun p := ⟨((whitneyFst A D).totalSpaceMap p, (whitneySnd A D).totalSpaceMap p), by
    rcases p with ⟨x, v⟩
    rw [Hom.totalSpaceMap_mk, Hom.totalSpaceMap_mk]⟩
  invFun pq :=
    ⟨pq.1.1.proj,
      ((splitCoords (𝕜 := 𝕜) (A.rank pq.1.1.proj) (D.rank pq.1.1.proj)).symm
        (pq.1.1.2, fun i ↦ pq.1.2.2 (Fin.cast (congrArg D.rank pq.2) i)) :
          (whitneySum A D).Fiber pq.1.1.proj)⟩
  left_inv p := by
    rcases p with ⟨x, v⟩
    have hfst := Hom.totalSpaceMap_mk (whitneyFst A D) x v
    have hsnd := Hom.totalSpaceMap_mk (whitneySnd A D) x v
    have hp : (⟨((whitneyFst A D).totalSpaceMap ⟨x, v⟩, (whitneySnd A D).totalSpaceMap ⟨x, v⟩),
        by rw [hfst, hsnd]⟩ :
          {pq : TotalSpace Unit A.Fiber × TotalSpace Unit D.Fiber // pq.1.proj = pq.2.proj}) =
        ⟨(⟨x, (whitneyFst A D).fiberMap x v⟩, ⟨x, (whitneySnd A D).fiberMap x v⟩), rfl⟩ :=
      Subtype.ext (Prod.ext hfst hsnd)
    -- Express the round-trip explicitly as a function of the fibre-product element to rewrite `hp`.
    change (fun pq :
        {pq : TotalSpace Unit A.Fiber × TotalSpace Unit D.Fiber // pq.1.proj = pq.2.proj} ↦
      (⟨pq.1.1.proj,
        ((splitCoords (𝕜 := 𝕜) (A.rank pq.1.1.proj) (D.rank pq.1.1.proj)).symm
          (pq.1.1.2, fun i ↦ pq.1.2.2 (Fin.cast (congrArg D.rank pq.2) i)) :
            (whitneySum A D).Fiber pq.1.1.proj)⟩ :
              TotalSpace Unit (whitneySum A D).Fiber))
        ⟨((whitneyFst A D).totalSpaceMap ⟨x, v⟩, (whitneySnd A D).totalSpaceMap ⟨x, v⟩), _⟩ =
      ⟨x, v⟩
    rw [hp]
    dsimp only
    rw [fiberMap_whitneyFst, fiberMap_whitneySnd]
    exact congrArg (TotalSpace.mk' (E := (whitneySum A D).Fiber) Unit x)
      ((splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm_apply_apply v)
  right_inv pq := by
    rcases pq with ⟨⟨⟨x₁, u⟩, ⟨x₂, w⟩⟩, hproj⟩
    dsimp only at hproj
    subst hproj
    let v : (whitneySum A D).Fiber x₁ :=
      (splitCoords (𝕜 := 𝕜) (A.rank x₁) (D.rank x₁)).symm (u, w)
    apply Subtype.ext
    apply Prod.ext
    · -- Fold the reconstructed vector into `v` so `Hom.totalSpaceMap_mk` applies cleanly.
      change (whitneyFst A D).totalSpaceMap ⟨x₁, v⟩ = ⟨x₁, u⟩
      rw [Hom.totalSpaceMap_mk, fiberMap_whitneyFst]
      exact congrArg (TotalSpace.mk' (E := A.Fiber) Unit x₁)
        (congrArg Prod.fst
          ((splitCoords (𝕜 := 𝕜) (A.rank x₁) (D.rank x₁)).apply_symm_apply (u, w)))
    · -- Fold the reconstructed vector into `v` on the second factor as well.
      change (whitneySnd A D).totalSpaceMap ⟨x₁, v⟩ = ⟨x₁, w⟩
      rw [Hom.totalSpaceMap_mk, fiberMap_whitneySnd]
      exact congrArg (TotalSpace.mk' (E := D.Fiber) Unit x₁)
        (congrArg Prod.snd
          ((splitCoords (𝕜 := 𝕜) (A.rank x₁) (D.rank x₁)).apply_symm_apply (u, w)))

/-- The reconstructed total space of `whitneySum A D` is homeomorphic over `X` to the topological
fibre product of the reconstructed total spaces of `A` and `D` over `X`. -/
noncomputable def whitneySumFiberProdHomeomorph (A D : FiniteRankAtlas 𝕜 X) :
    TotalSpace Unit (whitneySum A D).Fiber ≃ₜ
      {pq : TotalSpace Unit A.Fiber × TotalSpace Unit D.Fiber // pq.1.proj = pq.2.proj} where
  toEquiv := whitneyFiberProdEquiv A D
  continuous_toFun :=
    ((whitneyFst A D).totalSpaceMap.continuous.prodMk
      (whitneySnd A D).totalSpaceMap.continuous).subtype_mk _
  continuous_invFun := by
    let c := A.rank.prodMk D.rank
    have hb : Continuous (fun pq :
        {pq : TotalSpace Unit A.Fiber × TotalSpace Unit D.Fiber // pq.1.proj = pq.2.proj} ↦
          pq.1.1.proj) :=
      A.continuous_proj.comp (continuous_fst.comp continuous_subtype_val)
    let s (pq : {pq : TotalSpace Unit A.Fiber × TotalSpace Unit D.Fiber //
        pq.1.proj = pq.2.proj}) : (whitneySum A D).Fiber pq.1.1.proj :=
      (splitCoords (𝕜 := 𝕜) (A.rank pq.1.1.proj) (D.rank pq.1.1.proj)).symm
        (pq.1.1.2, fun i ↦ pq.1.2.2 (Fin.cast (congrArg D.rank pq.2) i))
    apply (continuous_mk_iff_clopenCores c hb _ s).2
    rintro ⟨m, n⟩
    let sub : C({x : X // c x = (m, n)}, X) := ⟨Subtype.val, continuous_subtype_val⟩
    let A_p := A.clopenPullCore c Prod.fst (fun _ ↦ rfl) (m, n)
    let D_p := D.clopenPullCore c Prod.snd (fun _ ↦ rfl) (m, n)
    let baseMap : {pq : {pq : TotalSpace Unit A.Fiber × TotalSpace Unit D.Fiber //
        pq.1.proj = pq.2.proj} // c pq.1.1.proj = (m, n)} → {x : X // c x = (m, n)} :=
      fun r ↦ ⟨r.1.1.1.proj, r.2⟩
    have hbase : Continuous baseMap := (hb.comp continuous_subtype_val).subtype_mk _
    have hA : Continuous (fun r : {pq : {pq : TotalSpace Unit A.Fiber × TotalSpace Unit D.Fiber //
        pq.1.proj = pq.2.proj} // c pq.1.1.proj = (m, n)} ↦
          (⟨baseMap r, fun i : Fin m ↦
            r.1.1.1.2 (Fin.cast (congrArg Prod.fst r.2).symm i)⟩ : A_p.core.TotalSpace)) := by
      refine A.continuous_into_pullCore sub m (fun x ↦ congrArg Prod.fst x.2) hbase ?_
      refine (continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)).congr
        fun r ↦ ?_
      rcases r with ⟨⟨⟨⟨x₁, u⟩, ⟨x₂, w⟩⟩, hproj⟩, hp⟩
      exact congrArg (TotalSpace.mk' (E := A.Fiber) Unit x₁)
        (funext fun i ↦ congrArg u (Fin.ext rfl))
    have hD : Continuous (fun r : {pq : {pq : TotalSpace Unit A.Fiber × TotalSpace Unit D.Fiber //
        pq.1.proj = pq.2.proj} // c pq.1.1.proj = (m, n)} ↦
          (⟨baseMap r, fun j : Fin n ↦ r.1.1.2.2
            (Fin.cast ((congrArg D.rank r.1.2).symm.trans (congrArg Prod.snd r.2)).symm j)⟩ :
              D_p.core.TotalSpace)) := by
      refine D.continuous_into_pullCore sub n (fun x ↦ congrArg Prod.snd x.2) hbase ?_
      refine (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)).congr
        fun r ↦ ?_
      rcases r with ⟨⟨⟨⟨x₁, u⟩, ⟨x₂, w⟩⟩, hproj⟩, hp⟩
      dsimp only at hproj
      subst hproj
      exact congrArg (TotalSpace.mk' (E := D.Fiber) Unit x₁)
        (funext fun j ↦ congrArg w (Fin.ext rfl))
    have hprod : Continuous (fun r :
        {pq : {pq : TotalSpace Unit A.Fiber × TotalSpace Unit D.Fiber //
          pq.1.proj = pq.2.proj} // c pq.1.1.proj = (m, n)} ↦
        (⟨baseMap r, (fun i : Fin m ↦ r.1.1.1.2 (Fin.cast (congrArg Prod.fst r.2).symm i),
          fun j : Fin n ↦ r.1.1.2.2
            (Fin.cast ((congrArg D.rank r.1.2).symm.trans (congrArg Prod.snd r.2)).symm j))⟩ :
              TotalSpace ((Fin m → 𝕜) × (Fin n → 𝕜)) (A_p.core.Fiber ×ᵇ D_p.core.Fiber))) := by
      rw [(FiberBundle.Prod.isInducing_diag (Fin m → 𝕜) A_p.core.Fiber
        (Fin n → 𝕜) D_p.core.Fiber).continuous_iff]
      exact hA.prodMk hD
    refine ((FiniteRankBundleCore.whitneySumTotalSpaceHomeomorph A_p D_p).symm.continuous.comp
      hprod).congr fun r ↦ ?_
    rcases r with ⟨⟨⟨⟨x₁, u⟩, ⟨x₂, w⟩⟩, hproj⟩, hp⟩
    dsimp only [c, LocallyConstant.prodMk_apply] at hproj hp
    subst hproj
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
    dsimp only [Function.comp_apply, baseMap, s]
    rw [FiniteRankBundleCore.whitneySumTotalSpaceHomeomorph_symm_apply,
      FiniteRankBundleCore.whitneySumFiberEquiv_symm_apply]
    rfl

@[simp]
theorem whitneySumFiberProdHomeomorph_apply (A D : FiniteRankAtlas 𝕜 X)
    (p : TotalSpace Unit (whitneySum A D).Fiber) :
    (whitneySumFiberProdHomeomorph A D p).1 =
      ((whitneyFst A D).totalSpaceMap p, (whitneySnd A D).totalSpaceMap p) :=
  (rfl)

@[simp]
theorem whitneySumFiberProdHomeomorph_symm_apply (A D : FiniteRankAtlas 𝕜 X)
    (x : X) (u : A.Fiber x) (w : D.Fiber x) :
    (whitneySumFiberProdHomeomorph A D).symm ⟨(⟨x, u⟩, ⟨x, w⟩), rfl⟩ =
      ⟨x, (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm (u, w)⟩ :=
  (rfl)

end TauCeti.FiniteRankAtlas
