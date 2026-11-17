/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Trivial
public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.WhitneySum
public import Mathlib.CategoryTheory.Preadditive.Biproducts

import TauCeti.Topology.LocallyConstant.Fiber

/-!
# Binary biproducts of variable-rank bundle atlases

From the two-component continuity characterizations `continuous_mk_whitneySum_iff` and
`continuous_whitneySum_iff` of `TauCeti.FiniteRankAtlas.whitneySum`, this file constructs the
canonical projections and inclusions (`whitneyFst`, `whitneySnd`, `whitneyInl`, `whitneyInr`), the
binary bicone (`whitneyBicone`, `whitneyBiconeIsBilimit`), and
`HasBinaryBiproducts (FiniteRankAtlas 𝕜 X)`.

It further exposes the canonical comparison isomorphism `whitneySumIsoBiprod` between
`whitneySum A D` and the categorical binary biproduct `A ⊞ D`, shows that
`whitneySumTotalSpaceHomeomorph` intertwines the conjugated `biprod.map` with the componentwise
fibre action (`whitneySumTotalSpaceHomeomorph_naturality`), and constructs the trivial-atlas sum
isomorphism `trivialAddIso` for `FiniteRankAtlas.trivial`. Universal-property pairing, copairing,
functorial direct sums, and symmetry, associativity, and unit coherence isomorphisms are supplied
directly by Mathlib's `CategoryTheory.Limits.biprod` API. No compactness, separation,
nonemptiness, bounded-rank, or scalar-completeness hypothesis is required.

The binary bicone construction parallels the constant-rank development for
`TauCeti.FiniteRankBundleCore` in `TauCeti.Topology.VectorBundle.FiniteRank.Biproduct`, lifting
coordinate splitting along `TauCeti.splitCoords` and
`CategoryTheory.Limits.isBinaryBilimitOfTotal` to variable-rank atlases.

## References

* M. F. Atiyah, *K-Theory*, §1.1–1.2.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, §3.
-/

public section

open Bundle CategoryTheory CategoryTheory.Limits

namespace TauCeti.FiniteRankAtlas

universe u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {X : Type u} [TopologicalSpace X]

section Bicone

/-- Projection of the Whitney sum onto its first summand. -/
def whitneyFst (A D : FiniteRankAtlas 𝕜 X) : whitneySum A D ⟶ A where
  fiberMap x := ((ContinuousLinearMap.fst 𝕜 (A.Fiber x) (D.Fiber x)).comp
    (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).toContinuousLinearMap).toLinearMap
  continuous_totalSpaceMap := ((continuous_whitneySum_iff.1 continuous_id).1).congr fun p =>
    congrArg (TotalSpace.mk' Unit p.proj)
      (congrArg Prod.fst (whitneySumFiberEquiv_apply A D p.proj p.2))

/-- Projection of the Whitney sum onto its second summand. -/
def whitneySnd (A D : FiniteRankAtlas 𝕜 X) : whitneySum A D ⟶ D where
  fiberMap x := ((ContinuousLinearMap.snd 𝕜 (A.Fiber x) (D.Fiber x)).comp
    (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).toContinuousLinearMap).toLinearMap
  continuous_totalSpaceMap := ((continuous_whitneySum_iff.1 continuous_id).2).congr fun p =>
    congrArg (TotalSpace.mk' Unit p.proj)
      (congrArg Prod.snd (whitneySumFiberEquiv_apply A D p.proj p.2))

/-- Inclusion of the first summand into the Whitney sum. -/
def whitneyInl (A D : FiniteRankAtlas 𝕜 X) : A ⟶ whitneySum A D where
  fiberMap x := ((splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl 𝕜 (A.Fiber x) (D.Fiber x))).toLinearMap
  continuous_totalSpaceMap := ((continuous_mk_whitneySum_iff (b := TotalSpace.proj)
    (fun p : TotalSpace Unit A.Fiber => p.2) (fun _ => 0)).2
    ⟨continuous_id, D.continuous_zeroSection.comp A.continuous_proj⟩).congr fun p =>
    congrArg (TotalSpace.mk' Unit p.proj) (whitneySumFiberEquiv_symm_apply A D p.proj (p.2, 0))

/-- Inclusion of the second summand into the Whitney sum. -/
def whitneyInr (A D : FiniteRankAtlas 𝕜 X) : D ⟶ whitneySum A D where
  fiberMap x := ((splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr 𝕜 (A.Fiber x) (D.Fiber x))).toLinearMap
  continuous_totalSpaceMap := ((continuous_mk_whitneySum_iff (b := TotalSpace.proj)
    (fun _ : TotalSpace Unit D.Fiber => 0) (fun p => p.2)).2
    ⟨A.continuous_zeroSection.comp D.continuous_proj, continuous_id⟩).congr fun p =>
    congrArg (TotalSpace.mk' Unit p.proj) (whitneySumFiberEquiv_symm_apply A D p.proj (0, p.2))

/-- On each fibre, `whitneyFst` extracts the first coordinate block. -/
@[simp] theorem fiberMap_whitneyFst (A D : FiniteRankAtlas 𝕜 X) (x : X) :
    (whitneyFst A D).fiberMap x =
      ((ContinuousLinearMap.fst 𝕜 (A.Fiber x) (D.Fiber x)).comp
        (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).toContinuousLinearMap).toLinearMap := (rfl)

/-- On each fibre, `whitneySnd` extracts the second coordinate block. -/
@[simp] theorem fiberMap_whitneySnd (A D : FiniteRankAtlas 𝕜 X) (x : X) :
    (whitneySnd A D).fiberMap x =
      ((ContinuousLinearMap.snd 𝕜 (A.Fiber x) (D.Fiber x)).comp
        (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).toContinuousLinearMap).toLinearMap := (rfl)

/-- On each fibre, `whitneyInl` appends a zero block. -/
@[simp] theorem fiberMap_whitneyInl (A D : FiniteRankAtlas 𝕜 X) (x : X) :
    (whitneyInl A D).fiberMap x =
      ((splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.inl 𝕜 (A.Fiber x) (D.Fiber x))).toLinearMap := (rfl)

/-- On each fibre, `whitneyInr` prepends a zero block. -/
@[simp] theorem fiberMap_whitneyInr (A D : FiniteRankAtlas 𝕜 X) (x : X) :
    (whitneyInr A D).fiberMap x =
      ((splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.inr 𝕜 (A.Fiber x) (D.Fiber x))).toLinearMap := (rfl)

theorem fst_whitneySumFiberEquiv (A D : FiniteRankAtlas 𝕜 X) (x : X)
    (v : (whitneySum A D).Fiber x) :
    (whitneySumFiberEquiv A D x v).1 = (whitneyFst A D).fiberMap x v := by
  -- Work in the standard coordinate model so `simp` does not stall on `(whitneySum A D).rank`.
  have h (v' : Fin (A.rank x + D.rank x) → 𝕜) :
      (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x) v').1 =
        (((ContinuousLinearMap.fst 𝕜 (A.Fiber x) (D.Fiber x)).comp
          (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).toContinuousLinearMap).toLinearMap) v' := by
    simp
  rw [whitneySumFiberEquiv_apply, fiberMap_whitneyFst]
  exact h v

theorem snd_whitneySumFiberEquiv (A D : FiniteRankAtlas 𝕜 X) (x : X)
    (v : (whitneySum A D).Fiber x) :
    (whitneySumFiberEquiv A D x v).2 = (whitneySnd A D).fiberMap x v := by
  have h (v' : Fin (A.rank x + D.rank x) → 𝕜) :
      (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x) v').2 =
        (((ContinuousLinearMap.snd 𝕜 (A.Fiber x) (D.Fiber x)).comp
          (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).toContinuousLinearMap).toLinearMap) v' := by
    simp
  rw [whitneySumFiberEquiv_apply, fiberMap_whitneySnd]
  exact h v

theorem whitneySumFiberEquiv_whitneyInl (A D : FiniteRankAtlas 𝕜 X) (x : X) (u : A.Fiber x) :
    whitneySumFiberEquiv A D x ((whitneyInl A D).fiberMap x u) = (u, 0) := by
  have h : splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)
      ((((splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.inl 𝕜 (A.Fiber x) (D.Fiber x))).toLinearMap) u) = (u, 0) := by
    simp
  rw [whitneySumFiberEquiv_apply, fiberMap_whitneyInl]
  exact h

theorem whitneySumFiberEquiv_whitneyInr (A D : FiniteRankAtlas 𝕜 X) (x : X) (w : D.Fiber x) :
    whitneySumFiberEquiv A D x ((whitneyInr A D).fiberMap x w) = (0, w) := by
  have h : splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)
      ((((splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.inr 𝕜 (A.Fiber x) (D.Fiber x))).toLinearMap) w) = (0, w) := by
    simp
  rw [whitneySumFiberEquiv_apply, fiberMap_whitneyInr]
  exact h

@[reassoc (attr := simp)] theorem whitneyInl_fst (A D : FiniteRankAtlas 𝕜 X) :
    whitneyInl A D ≫ whitneyFst A D = 𝟙 A := by
  apply hom_ext; intro x; apply LinearMap.ext; intro u
  simp only [fiberMap_comp, fiberMap_id, LinearMap.comp_apply, LinearMap.id_apply,
    ← fst_whitneySumFiberEquiv, whitneySumFiberEquiv_whitneyInl]

@[reassoc (attr := simp)] theorem whitneyInl_snd (A D : FiniteRankAtlas 𝕜 X) :
    whitneyInl A D ≫ whitneySnd A D = 0 := by
  apply hom_ext; intro x; apply LinearMap.ext; intro u
  simp only [fiberMap_comp, fiberMap_zero, LinearMap.comp_apply, LinearMap.zero_apply,
    ← snd_whitneySumFiberEquiv, whitneySumFiberEquiv_whitneyInl]

@[reassoc (attr := simp)] theorem whitneyInr_fst (A D : FiniteRankAtlas 𝕜 X) :
    whitneyInr A D ≫ whitneyFst A D = 0 := by
  apply hom_ext; intro x; apply LinearMap.ext; intro w
  simp only [fiberMap_comp, fiberMap_zero, LinearMap.comp_apply, LinearMap.zero_apply,
    ← fst_whitneySumFiberEquiv, whitneySumFiberEquiv_whitneyInr]

@[reassoc (attr := simp)] theorem whitneyInr_snd (A D : FiniteRankAtlas 𝕜 X) :
    whitneyInr A D ≫ whitneySnd A D = 𝟙 D := by
  apply hom_ext; intro x; apply LinearMap.ext; intro w
  simp only [fiberMap_comp, fiberMap_id, LinearMap.comp_apply, LinearMap.id_apply,
    ← snd_whitneySumFiberEquiv, whitneySumFiberEquiv_whitneyInr]

/-- The concrete binary bicone exhibiting `whitneySum A D` with its four canonical bundle maps. -/
-- Expose the point projection so the legs reduce to morphisms on `whitneySum A D`.
@[expose] def whitneyBicone (A D : FiniteRankAtlas 𝕜 X) : BinaryBicone A D where
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

/-- The coordinate-block projections and inclusions of `whitneySum A D` resolve the identity. -/
@[simp] theorem whitney_total (A D : FiniteRankAtlas 𝕜 X) :
    whitneyFst A D ≫ whitneyInl A D + whitneySnd A D ≫ whitneyInr A D =
      𝟙 (whitneySum A D) := by
  apply hom_ext
  intro x
  apply LinearMap.ext
  intro v
  apply (whitneySumFiberEquiv A D x).injective
  simp only [fiberMap_add, fiberMap_comp, fiberMap_id, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.id_apply, map_add, whitneySumFiberEquiv_whitneyInl, whitneySumFiberEquiv_whitneyInr,
    ← fst_whitneySumFiberEquiv, ← snd_whitneySumFiberEquiv, Prod.mk_add_mk, add_zero, zero_add,
    Prod.mk.eta]

/-- The Whitney sum bicone is a categorical binary biproduct in `FiniteRankAtlas 𝕜 X`. -/
def whitneyBiconeIsBilimit (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyBicone A D).IsBilimit :=
  isBinaryBilimitOfTotal _ (whitney_total A D)

/-- Whitney sums provide binary biproducts of variable-rank bundle atlases. -/
instance : HasBinaryBiproducts (FiniteRankAtlas 𝕜 X) where
  has_binary_biproduct A D := ⟨⟨whitneyBicone A D, whitneyBiconeIsBilimit A D⟩⟩

/-- The Whitney sum `whitneySum A D` is isomorphic to the categorical binary biproduct
`A ⊞ D`. -/
noncomputable def whitneySumIsoBiprod (A D : FiniteRankAtlas 𝕜 X) : whitneySum A D ≅ A ⊞ D :=
  biprod.uniqueUpToIso A D (whitneyBiconeIsBilimit A D)

/-- The forward isomorphism `whitneySum A D ⟶ A ⊞ D` is the biproduct lift of `whitneyFst` and
`whitneySnd`. -/
@[simp] theorem whitneySumIsoBiprod_hom (A D : FiniteRankAtlas 𝕜 X) :
    (whitneySumIsoBiprod A D).hom = biprod.lift (whitneyFst A D) (whitneySnd A D) := (rfl)

/-- The inverse isomorphism `A ⊞ D ⟶ whitneySum A D` is the biproduct desc of `whitneyInl` and
`whitneyInr`. -/
@[simp] theorem whitneySumIsoBiprod_inv (A D : FiniteRankAtlas 𝕜 X) :
    (whitneySumIsoBiprod A D).inv = biprod.desc (whitneyInl A D) (whitneyInr A D) := (rfl)

/-- The locally constant rank of a categorical binary biproduct is the sum of the summand ranks. -/
@[simp] theorem rank_biprod (A D : FiniteRankAtlas 𝕜 X) :
    (A ⊞ D).rank = A.rank + D.rank :=
  (whitneySumIsoBiprod A D).symm.finiteRankAtlas_rank_eq

/-- `whitneySumTotalSpaceHomeomorph` intertwines the conjugated biproduct map
`(whitneySumIsoBiprod A D).hom ≫ biprod.map f g ≫ (whitneySumIsoBiprod A' D').inv` with the
componentwise action of `f` and `g` on the fibrewise-product total space
`TotalSpace (Unit × Unit) (A.Fiber ×ᵇ D.Fiber)` equipped with
`FiberBundle.Prod.topologicalSpace`. -/
theorem whitneySumTotalSpaceHomeomorph_naturality {A A' D D' : FiniteRankAtlas 𝕜 X}
    (f : A ⟶ A') (g : D ⟶ D') (p : TotalSpace Unit (whitneySum A D).Fiber) :
    whitneySumTotalSpaceHomeomorph A' D'
        (((whitneySumIsoBiprod A D).hom ≫ biprod.map f g ≫
          (whitneySumIsoBiprod A' D').inv).totalSpaceMap p) =
      ⟨(whitneySumTotalSpaceHomeomorph A D p).proj,
        (f.fiberMap (whitneySumTotalSpaceHomeomorph A D p).proj
          (whitneySumTotalSpaceHomeomorph A D p).2.1,
         g.fiberMap (whitneySumTotalSpaceHomeomorph A D p).proj
          (whitneySumTotalSpaceHomeomorph A D p).2.2)⟩ := by
  rcases p with ⟨x, v⟩
  have hfst : ((whitneySumIsoBiprod A D).hom ≫ biprod.map f g ≫
      (whitneySumIsoBiprod A' D').inv) ≫ whitneyFst A' D' = whitneyFst A D ≫ f := by
    have hinv : (whitneySumIsoBiprod A' D').inv ≫ whitneyFst A' D' = biprod.fst :=
      biprod.hom_ext' _ _ (by simp) (by simp)
    rw [Category.assoc, Category.assoc, hinv]
    simp
  have hsnd : ((whitneySumIsoBiprod A D).hom ≫ biprod.map f g ≫
      (whitneySumIsoBiprod A' D').inv) ≫ whitneySnd A' D' = whitneySnd A D ≫ g := by
    have hinv : (whitneySumIsoBiprod A' D').inv ≫ whitneySnd A' D' = biprod.snd :=
      biprod.hom_ext' _ _ (by simp) (by simp)
    rw [Category.assoc, Category.assoc, hinv]
    simp
  rw [Hom.totalSpaceMap_mk, whitneySumTotalSpaceHomeomorph_apply,
    whitneySumTotalSpaceHomeomorph_apply]
  dsimp only
  refine congrArg (TotalSpace.mk' (Unit × Unit) x) (Prod.ext ?_ ?_)
  · rw [fst_whitneySumFiberEquiv, fst_whitneySumFiberEquiv, ← LinearMap.comp_apply,
      ← fiberMap_comp, hfst, fiberMap_comp, LinearMap.comp_apply]
  · rw [snd_whitneySumFiberEquiv, snd_whitneySumFiberEquiv, ← LinearMap.comp_apply,
      ← fiberMap_comp, hsnd, fiberMap_comp, LinearMap.comp_apply]

end Bicone

section Trivial

private theorem continuous_trivialAdd_toFun (r s : LocallyConstant X ℕ) :
    Continuous (fun p : TotalSpace Unit (trivial 𝕜 (r + s)).Fiber =>
      (⟨p.proj, p.2⟩ : TotalSpace Unit (whitneySum (trivial 𝕜 r) (trivial 𝕜 s)).Fiber)) := by
  have hrs := (continuous_trivial_iff
    (f := fun p : TotalSpace Unit (trivial 𝕜 (r + s)).Fiber => p)).1 continuous_id'
  apply ((r.isLocallyConstant.comp_continuous hrs.1).continuous_iff₂
    (s.isLocallyConstant.comp_continuous hrs.1)).2
  intro a d
  let Z := {p : TotalSpace Unit (trivial 𝕜 (r + s)).Fiber // r p.proj = a ∧ s p.proj = d}
  have hrs' : ∀ z : Z, (r + s) z.1.proj = a + d := fun z => by simp [z.2.1, z.2.2]
  let uv : Z → (Fin a → 𝕜) × (Fin d → 𝕜) :=
    fun z => splitCoords (𝕜 := 𝕜) a d (fun i => z.1.2 (Fin.cast (hrs' z).symm i))
  have hb : Continuous (fun z : Z => z.1.proj) := hrs.1.comp continuous_subtype_val
  have huv : Continuous uv := (splitCoords (𝕜 := 𝕜) a d).continuous.comp
    ((hrs.2 (a + d)).comp (continuous_subtype_val.subtype_mk hrs'))
  refine ((continuous_mk_whitneySum_iff (A := trivial 𝕜 r) (D := trivial 𝕜 s)
    (b := fun z : Z => z.1.proj)
    (fun z i => (uv z).1 (Fin.cast z.2.1 i))
    (fun z i => (uv z).2 (Fin.cast z.2.2 i))).2
      ⟨(continuous_mk_trivial_iff_of_rank_eq fun z => z.2.1).2 ⟨hb, huv.fst⟩,
       (continuous_mk_trivial_iff_of_rank_eq fun z => z.2.2).2 ⟨hb, huv.snd⟩⟩).congr fun z => ?_
  rcases z with ⟨⟨x, v⟩, ha, hd⟩
  dsimp only [Z] at ha hd
  subst ha; subst hd
  refine congrArg (TotalSpace.mk' Unit x) ?_
  rw [whitneySumFiberEquiv_symm_apply]
  have hv : (fun i : Fin (r x + s x) => v (Fin.cast (hrs' ⟨⟨x, v⟩, rfl, rfl⟩).symm i)) = v :=
    funext fun _ => congrArg v (Fin.ext rfl)
  have h (w : Fin (r x + s x) → 𝕜) :
      (splitCoords (𝕜 := 𝕜) (M := 𝕜) (r x) (s x)).symm
        (fun i => (splitCoords (𝕜 := 𝕜) (M := 𝕜) (r x) (s x) w).1 (Fin.cast rfl i),
         fun i => (splitCoords (𝕜 := 𝕜) (M := 𝕜) (r x) (s x) w).2 (Fin.cast rfl i)) = w := by
    simp only [Fin.cast_refl, id_eq, Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply]
  exact (h _).trans hv

private theorem continuous_trivialAdd_invFun (r s : LocallyConstant X ℕ) :
    Continuous (fun p : TotalSpace Unit (whitneySum (trivial 𝕜 r) (trivial 𝕜 s)).Fiber =>
      (⟨p.proj, p.2⟩ : TotalSpace Unit (trivial 𝕜 (r + s)).Fiber)) := by
  have hw := (continuous_whitneySum_iff
    (f := fun p : TotalSpace Unit (whitneySum (trivial 𝕜 r) (trivial 𝕜 s)).Fiber => p)).1
    continuous_id'
  have hr := continuous_trivial_iff.1 hw.1
  have hs := continuous_trivial_iff.1 hw.2
  have hproj := (whitneySum (trivial 𝕜 r) (trivial 𝕜 s)).continuous_proj
  apply ((r.isLocallyConstant.comp_continuous hproj).continuous_iff₂
    (s.isLocallyConstant.comp_continuous hproj)).2
  intro a d
  let Z := {p : TotalSpace Unit (whitneySum (trivial 𝕜 r) (trivial 𝕜 s)).Fiber //
    r p.proj = a ∧ s p.proj = d}
  have hrs : ∀ z : Z, (r + s) z.1.proj = a + d := fun z => by simp [z.2.1, z.2.2]
  have hc := (splitCoords (𝕜 := 𝕜) a d).symm.continuous.comp
    (((hr.2 a).comp (continuous_subtype_val.subtype_mk fun z : Z => z.2.1)).prodMk
      ((hs.2 d).comp (continuous_subtype_val.subtype_mk fun z : Z => z.2.2)))
  refine ((continuous_mk_trivial_iff_of_rank_eq hrs).2
    ⟨hproj.comp continuous_subtype_val, hc⟩).congr fun z => ?_
  rcases z with ⟨⟨x, v⟩, ha, hd⟩
  dsimp only [Z] at ha hd
  subst ha; subst hd
  refine congrArg (TotalSpace.mk' Unit x) (funext fun i => ?_)
  dsimp only [Function.comp_apply]
  rw [whitneySumFiberEquiv_apply]
  have h (w : Fin (r x + s x) → 𝕜) :
      (splitCoords (𝕜 := 𝕜) (M := 𝕜) (r x) (s x)).symm
        (fun j => (splitCoords (𝕜 := 𝕜) (M := 𝕜) (r x) (s x) w).1 (Fin.cast rfl j),
         fun j => (splitCoords (𝕜 := 𝕜) (M := 𝕜) (r x) (s x) w).2 (Fin.cast rfl j)) = w := by
    simp only [Fin.cast_refl, id_eq, Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply]
  exact (congrFun (h v) (Fin.cast (hrs ⟨⟨x, v⟩, rfl, rfl⟩) i)).trans
    (congrArg (v : Fin (r x + s x) → 𝕜) (Fin.ext rfl))

variable (𝕜) in
/-- The trivial atlas of rank `r + s` is isomorphic, by the identity on every coordinate fibre, to
the Whitney sum of the trivial atlases of ranks `r` and `s`. -/
def trivialAddIso (r s : LocallyConstant X ℕ) :
    trivial 𝕜 (r + s) ≅ whitneySum (trivial 𝕜 r) (trivial 𝕜 s) :=
  isoMk (fun x => LinearEquiv.refl 𝕜 (Fin (r x + s x) → 𝕜))
    (continuous_trivialAdd_toFun r s)
    (continuous_trivialAdd_invFun r s)

@[simp]
theorem fiberMap_trivialAddIso_hom (r s : LocallyConstant X ℕ) (x : X) :
    (trivialAddIso 𝕜 r s).hom.fiberMap x = LinearMap.id :=
  fiberMap_isoMk_hom _ _ _ x

@[simp]
theorem fiberMap_trivialAddIso_inv (r s : LocallyConstant X ℕ) (x : X) :
    (trivialAddIso 𝕜 r s).inv.fiberMap x = LinearMap.id :=
  fiberMap_isoMk_inv _ _ _ x

end Trivial

end TauCeti.FiniteRankAtlas
