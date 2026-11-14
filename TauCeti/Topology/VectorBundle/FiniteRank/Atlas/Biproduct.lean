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
# Binary biproducts and coherence of variable-rank bundle atlases

From the two-component continuity characterizations `continuous_mk_whitneySum_iff` and
`continuous_whitneySum_iff` of `TauCeti.FiniteRankAtlas.whitneySum`, this file constructs the
canonical projections and inclusions (`whitneyFst`, `whitneySnd`, `whitneyInl`, `whitneyInr`), the
binary bicone (`whitneyBicone`, `whitneyBiconeIsBilimit`), and
`HasBinaryBiproducts (FiniteRankAtlas 𝕜 X)`.

It further provides concrete pairing (`whitneyLift`), copairing (`whitneyDesc`), functorial direct
sums (`whitneyMap`, `whitneyMapIso`) intertwining `whitneySumTotalSpaceHomeomorph`
(`whitneySumTotalSpaceHomeomorph_naturality`), symmetry, associativity, and unit coherence
isomorphisms (`whitneyCommIso`, `whitneyAssocIso`, `whitneyZeroLeftIsoOfIsZero`,
`whitneyZeroRightIsoOfIsZero`, `whitneyZeroLeftIso`, `whitneyZeroRightIso`), and the trivial-atlas
sum isomorphism `trivialAddIso` for `FiniteRankAtlas.trivial`. No compactness, separation,
nonemptiness, bounded-rank, or scalar-completeness hypothesis is required.

The universal-property and coherence API parallels the constant-rank development for
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

/-- The locally constant rank of a categorical binary biproduct is the sum of the summand ranks. -/
@[simp] theorem rank_biprod (A D : FiniteRankAtlas 𝕜 X) :
    (A ⊞ D).rank = A.rank + D.rank :=
  (biprod.uniqueUpToIso A D (whitneyBiconeIsBilimit A D)).symm.finiteRankAtlas_rank_eq

end Bicone

section UniversalProperty

variable {A A' A'' D D' D'' C E : FiniteRankAtlas 𝕜 X}

/-- Pair two bundle morphisms with common source into the concrete Whitney sum. -/
def whitneyLift (f : E ⟶ A) (g : E ⟶ D) : E ⟶ whitneySum A D :=
  f ≫ whitneyInl A D + g ≫ whitneyInr A D

theorem whitneyLift_def (f : E ⟶ A) (g : E ⟶ D) :
    whitneyLift f g = f ≫ whitneyInl A D + g ≫ whitneyInr A D := (rfl)

@[reassoc (attr := simp)]
theorem whitneyLift_fst (f : E ⟶ A) (g : E ⟶ D) :
    whitneyLift f g ≫ whitneyFst A D = f := by
  simp [whitneyLift, Preadditive.add_comp]

@[reassoc (attr := simp)]
theorem whitneyLift_snd (f : E ⟶ A) (g : E ⟶ D) :
    whitneyLift f g ≫ whitneySnd A D = g := by
  simp [whitneyLift, Preadditive.add_comp]

/-- Every morphism into a Whitney sum is the pairing of its two projections. -/
theorem eq_whitneyLift (h : E ⟶ whitneySum A D) :
    h = whitneyLift (h ≫ whitneyFst A D) (h ≫ whitneySnd A D) := by
  calc
    h = h ≫ 𝟙 (whitneySum A D) := (Category.comp_id h).symm
    _ = h ≫ (whitneyFst A D ≫ whitneyInl A D + whitneySnd A D ≫ whitneyInr A D) := by
      rw [whitney_total]
    _ = whitneyLift (h ≫ whitneyFst A D) (h ≫ whitneySnd A D) := by
      simp only [whitneyLift, Preadditive.comp_add, Category.assoc]

/-- Morphisms into a Whitney sum are determined by their compositions with the two projections. -/
theorem whitneySum_hom_ext {h₁ h₂ : E ⟶ whitneySum A D}
    (hfst : h₁ ≫ whitneyFst A D = h₂ ≫ whitneyFst A D)
    (hsnd : h₁ ≫ whitneySnd A D = h₂ ≫ whitneySnd A D) : h₁ = h₂ := by
  rw [eq_whitneyLift h₁, eq_whitneyLift h₂, hfst, hsnd]

@[reassoc]
theorem comp_whitneyLift (h : C ⟶ E) (f : E ⟶ A) (g : E ⟶ D) :
    h ≫ whitneyLift f g = whitneyLift (h ≫ f) (h ≫ g) := by
  simp only [whitneyLift, Preadditive.comp_add, Category.assoc]

@[simp]
theorem whitneyLift_fst_snd (A D : FiniteRankAtlas 𝕜 X) :
    whitneyLift (whitneyFst A D) (whitneySnd A D) = 𝟙 (whitneySum A D) :=
  whitney_total A D

@[simp]
theorem whitneyLift_zero (E A D : FiniteRankAtlas 𝕜 X) :
    whitneyLift (0 : E ⟶ A) (0 : E ⟶ D) = 0 :=
  whitneySum_hom_ext (by simp) (by simp)

/-- On each fibre, `whitneyLift f g` pairs `f.fiberMap x` and `g.fiberMap x` via `splitCoords`. -/
@[simp]
theorem fiberMap_whitneyLift (f : E ⟶ A) (g : E ⟶ D) (x : X) :
    (whitneyLift f g).fiberMap x =
      (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm.toLinearEquiv.toLinearMap.comp
        ((f.fiberMap x).prod (g.fiberMap x)) := by
  -- Work in the standard coordinate model so `simp` does not stall on `(whitneySum A D).rank`.
  let e := splitCoords (𝕜 := 𝕜) (M := 𝕜) (A.rank x) (D.rank x)
  have h : ((e.symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.inl 𝕜 (A.Fiber x) (D.Fiber x))).toLinearMap.comp (f.fiberMap x) +
      (e.symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.inr 𝕜 (A.Fiber x) (D.Fiber x))).toLinearMap.comp (g.fiberMap x)) =
      e.symm.toLinearEquiv.toLinearMap.comp ((f.fiberMap x).prod (g.fiberMap x)) := by
    apply LinearMap.ext
    intro v
    apply e.injective
    simp [map_add]
  simp only [whitneyLift_def, fiberMap_add, fiberMap_comp, fiberMap_whitneyInl, fiberMap_whitneyInr]
  exact h

/-- Copair two bundle morphisms with common target out of the concrete Whitney sum. -/
def whitneyDesc (f : A ⟶ E) (g : D ⟶ E) : whitneySum A D ⟶ E :=
  whitneyFst A D ≫ f + whitneySnd A D ≫ g

theorem whitneyDesc_def (f : A ⟶ E) (g : D ⟶ E) :
    whitneyDesc f g = whitneyFst A D ≫ f + whitneySnd A D ≫ g := (rfl)

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

/-- Every morphism out of a Whitney sum is the copairing of its two summand restrictions. -/
theorem eq_whitneyDesc (h : whitneySum A D ⟶ E) :
    h = whitneyDesc (whitneyInl A D ≫ h) (whitneyInr A D ≫ h) := by
  calc
    h = 𝟙 (whitneySum A D) ≫ h := (Category.id_comp h).symm
    _ = (whitneyFst A D ≫ whitneyInl A D + whitneySnd A D ≫ whitneyInr A D) ≫ h := by
      rw [whitney_total]
    _ = whitneyDesc (whitneyInl A D ≫ h) (whitneyInr A D ≫ h) := by
      simp only [whitneyDesc, Preadditive.add_comp, Category.assoc]

/-- Morphisms out of a Whitney sum are determined by their restrictions to the two summands. -/
theorem whitneySum_hom_ext' {h₁ h₂ : whitneySum A D ⟶ E}
    (hinl : whitneyInl A D ≫ h₁ = whitneyInl A D ≫ h₂)
    (hinr : whitneyInr A D ≫ h₁ = whitneyInr A D ≫ h₂) : h₁ = h₂ := by
  rw [eq_whitneyDesc h₁, eq_whitneyDesc h₂, hinl, hinr]

@[reassoc]
theorem whitneyDesc_comp (f : A ⟶ E) (g : D ⟶ E) (h : E ⟶ C) :
    whitneyDesc f g ≫ h = whitneyDesc (f ≫ h) (g ≫ h) := by
  simp only [whitneyDesc, Preadditive.add_comp, Category.assoc]

@[simp]
theorem whitneyDesc_inl_inr (A D : FiniteRankAtlas 𝕜 X) :
    whitneyDesc (whitneyInl A D) (whitneyInr A D) = 𝟙 (whitneySum A D) :=
  whitney_total A D

@[simp]
theorem whitneyDesc_zero (A D E : FiniteRankAtlas 𝕜 X) :
    whitneyDesc (0 : A ⟶ E) (0 : D ⟶ E) = 0 :=
  whitneySum_hom_ext' (by simp) (by simp)

/-- On each fibre, `whitneyDesc f g` copairs `f.fiberMap x` and `g.fiberMap x` after
`splitCoords`. -/
@[simp]
theorem fiberMap_whitneyDesc (f : A ⟶ E) (g : D ⟶ E) (x : X) :
    (whitneyDesc f g).fiberMap x =
      ((f.fiberMap x).coprod (g.fiberMap x)).comp
        (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).toLinearEquiv.toLinearMap := by
  let e := splitCoords (𝕜 := 𝕜) (M := 𝕜) (A.rank x) (D.rank x)
  have h : (f.fiberMap x).comp
        (((ContinuousLinearMap.fst 𝕜 (A.Fiber x) (D.Fiber x)).comp
          e.toContinuousLinearMap).toLinearMap) +
      (g.fiberMap x).comp
        (((ContinuousLinearMap.snd 𝕜 (A.Fiber x) (D.Fiber x)).comp
          e.toContinuousLinearMap).toLinearMap) =
      ((f.fiberMap x).coprod (g.fiberMap x)).comp e.toLinearEquiv.toLinearMap := by
    apply LinearMap.ext
    intro v
    simp
  simp only [whitneyDesc_def, fiberMap_add, fiberMap_comp, fiberMap_whitneyFst, fiberMap_whitneySnd]
  exact h

/-- Direct sum of two bundle morphisms on Whitney sums. -/
def whitneyMap (f : A ⟶ A') (g : D ⟶ D') : whitneySum A D ⟶ whitneySum A' D' :=
  whitneyLift (whitneyFst A D ≫ f) (whitneySnd A D ≫ g)

theorem whitneyMap_def (f : A ⟶ A') (g : D ⟶ D') :
    whitneyMap f g = whitneyLift (whitneyFst A D ≫ f) (whitneySnd A D ≫ g) := (rfl)

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
    whitneyMap (𝟙 A) (𝟙 D) = 𝟙 (whitneySum A D) := by
  simp [whitneyMap_def]

@[simp]
theorem whitneyMap_zero (A A' D D' : FiniteRankAtlas 𝕜 X) :
    whitneyMap (0 : A ⟶ A') (0 : D ⟶ D') = 0 :=
  whitneySum_hom_ext (by simp) (by simp)

@[reassoc (attr := simp)]
theorem whitneyMap_comp (f₁ : A ⟶ A') (f₂ : A' ⟶ A'') (g₁ : D ⟶ D') (g₂ : D' ⟶ D'') :
    whitneyMap f₁ g₁ ≫ whitneyMap f₂ g₂ = whitneyMap (f₁ ≫ f₂) (g₁ ≫ g₂) :=
  whitneySum_hom_ext (by simp) (by simp)

/-- On each fibre, `whitneyMap f g` acts as `Prod.map` conjugated by `splitCoords`. -/
@[simp]
theorem fiberMap_whitneyMap (f : A ⟶ A') (g : D ⟶ D') (x : X) :
    (whitneyMap f g).fiberMap x =
      (splitCoords (𝕜 := 𝕜) (A'.rank x) (D'.rank x)).symm.toLinearEquiv.toLinearMap.comp
        (((f.fiberMap x).prodMap (g.fiberMap x)).comp
          (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).toLinearEquiv.toLinearMap) := by
  let e := splitCoords (𝕜 := 𝕜) (M := 𝕜) (A.rank x) (D.rank x)
  let e' := splitCoords (𝕜 := 𝕜) (M := 𝕜) (A'.rank x) (D'.rank x)
  have h : e'.symm.toLinearEquiv.toLinearMap.comp
        (((f.fiberMap x).comp
          (((ContinuousLinearMap.fst 𝕜 (A.Fiber x) (D.Fiber x)).comp
            e.toContinuousLinearMap).toLinearMap)).prod
          ((g.fiberMap x).comp
            (((ContinuousLinearMap.snd 𝕜 (A.Fiber x) (D.Fiber x)).comp
              e.toContinuousLinearMap).toLinearMap))) =
      e'.symm.toLinearEquiv.toLinearMap.comp
        (((f.fiberMap x).prodMap (g.fiberMap x)).comp e.toLinearEquiv.toLinearMap) := by
    apply LinearMap.ext
    intro v
    apply e'.injective
    simp
  simp only [whitneyMap_def, fiberMap_whitneyLift, fiberMap_comp, fiberMap_whitneyFst,
    fiberMap_whitneySnd]
  exact h

/-- `whitneySumTotalSpaceHomeomorph` intertwines `whitneyMap f g` with the componentwise action of
`f` and `g` on Mathlib's direct-sum bundle. -/
theorem whitneySumTotalSpaceHomeomorph_naturality (f : A ⟶ A') (g : D ⟶ D')
    (p : TotalSpace Unit (whitneySum A D).Fiber) :
    whitneySumTotalSpaceHomeomorph A' D' ((whitneyMap f g).totalSpaceMap p) =
      ⟨(whitneySumTotalSpaceHomeomorph A D p).proj,
        (f.fiberMap (whitneySumTotalSpaceHomeomorph A D p).proj
          (whitneySumTotalSpaceHomeomorph A D p).2.1,
         g.fiberMap (whitneySumTotalSpaceHomeomorph A D p).proj
          (whitneySumTotalSpaceHomeomorph A D p).2.2)⟩ := by
  rcases p with ⟨x, v⟩
  rw [Hom.totalSpaceMap_mk, whitneySumTotalSpaceHomeomorph_apply,
    whitneySumTotalSpaceHomeomorph_apply]
  refine congrArg (TotalSpace.mk' (Unit × Unit) x) ?_
  have h (v' : Fin (A.rank x + D.rank x) → 𝕜) :
      splitCoords (𝕜 := 𝕜) (A'.rank x) (D'.rank x)
        (((splitCoords (𝕜 := 𝕜) (A'.rank x) (D'.rank x)).symm.toLinearEquiv.toLinearMap.comp
          (((f.fiberMap x).prodMap (g.fiberMap x)).comp
            (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).toLinearEquiv.toLinearMap)) v') =
        (f.fiberMap x (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x) v').1,
         g.fiberMap x (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x) v').2) := by
    simp
  rw [whitneySumFiberEquiv_apply, fiberMap_whitneyMap, whitneySumFiberEquiv_apply]
  exact h v

/-- Direct sum of two bundle atlas isomorphisms. -/
def whitneyMapIso (e₁ : A ≅ A') (e₂ : D ≅ D') : whitneySum A D ≅ whitneySum A' D' where
  hom := whitneyMap e₁.hom e₂.hom
  inv := whitneyMap e₁.inv e₂.inv
  hom_inv_id := by simp
  inv_hom_id := by simp

@[simp]
theorem whitneyMapIso_hom (e₁ : A ≅ A') (e₂ : D ≅ D') :
    (whitneyMapIso e₁ e₂).hom = whitneyMap e₁.hom e₂.hom := (rfl)

@[simp]
theorem whitneyMapIso_inv (e₁ : A ≅ A') (e₂ : D ≅ D') :
    (whitneyMapIso e₁ e₂).inv = whitneyMap e₁.inv e₂.inv := (rfl)

end UniversalProperty

section Coherence

/-- Symmetry isomorphism exchanging the two summands of a Whitney sum. -/
def whitneyCommIso (A D : FiniteRankAtlas 𝕜 X) : whitneySum A D ≅ whitneySum D A where
  hom := whitneyLift (whitneySnd A D) (whitneyFst A D)
  inv := whitneyLift (whitneySnd D A) (whitneyFst D A)
  hom_inv_id := whitneySum_hom_ext (by simp) (by simp)
  inv_hom_id := whitneySum_hom_ext (by simp) (by simp)

@[simp]
theorem whitneyCommIso_hom (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyCommIso A D).hom = whitneyLift (whitneySnd A D) (whitneyFst A D) := (rfl)

@[simp]
theorem whitneyCommIso_inv (A D : FiniteRankAtlas 𝕜 X) :
    (whitneyCommIso A D).inv = whitneyLift (whitneySnd D A) (whitneyFst D A) := (rfl)

@[reassoc]
theorem whitneyMap_commIso_hom {A A' D D' : FiniteRankAtlas 𝕜 X}
    (f : A ⟶ A') (g : D ⟶ D') :
    whitneyMap f g ≫ (whitneyCommIso A' D').hom =
      (whitneyCommIso A D).hom ≫ whitneyMap g f :=
  whitneySum_hom_ext (by simp) (by simp)

/-- Associativity isomorphism regrouping a threefold Whitney sum. -/
def whitneyAssocIso (A D C : FiniteRankAtlas 𝕜 X) :
    whitneySum (whitneySum A D) C ≅ whitneySum A (whitneySum D C) where
  hom := whitneyLift (whitneyFst _ _ ≫ whitneyFst A D)
    (whitneyLift (whitneyFst _ _ ≫ whitneySnd A D) (whitneySnd _ _))
  inv := whitneyLift (whitneyLift (whitneyFst _ _) (whitneySnd _ _ ≫ whitneyFst D C))
    (whitneySnd _ _ ≫ whitneySnd D C)
  hom_inv_id := whitneySum_hom_ext (whitneySum_hom_ext (by simp) (by simp)) (by simp)
  inv_hom_id := whitneySum_hom_ext (by simp) (whitneySum_hom_ext (by simp) (by simp))

@[simp]
theorem whitneyAssocIso_hom (A D C : FiniteRankAtlas 𝕜 X) :
    (whitneyAssocIso A D C).hom =
      whitneyLift (whitneyFst _ _ ≫ whitneyFst A D)
        (whitneyLift (whitneyFst _ _ ≫ whitneySnd A D) (whitneySnd _ _)) := (rfl)

@[simp]
theorem whitneyAssocIso_inv (A D C : FiniteRankAtlas 𝕜 X) :
    (whitneyAssocIso A D C).inv =
      whitneyLift (whitneyLift (whitneyFst _ _) (whitneySnd _ _ ≫ whitneyFst D C))
        (whitneySnd _ _ ≫ whitneySnd D C) := (rfl)

@[reassoc]
theorem whitneyMap_assocIso_hom {A A' D D' C C' : FiniteRankAtlas 𝕜 X}
    (f : A ⟶ A') (g : D ⟶ D') (h : C ⟶ C') :
    whitneyMap (whitneyMap f g) h ≫ (whitneyAssocIso A' D' C').hom =
      (whitneyAssocIso A D C).hom ≫ whitneyMap f (whitneyMap g h) :=
  whitneySum_hom_ext (by simp) (whitneySum_hom_ext (by simp) (by simp))

/-- Left unit isomorphism for Whitney sum with any zero bundle atlas. -/
def whitneyZeroLeftIsoOfIsZero {Z : FiniteRankAtlas 𝕜 X} (hZ : IsZero Z)
    (A : FiniteRankAtlas 𝕜 X) : whitneySum Z A ≅ A where
  hom := whitneySnd Z A
  inv := whitneyInr Z A
  hom_inv_id := whitneySum_hom_ext' (hZ.eq_of_src _ _) (by simp)
  inv_hom_id := whitneyInr_snd Z A

@[simp]
theorem whitneyZeroLeftIsoOfIsZero_hom {Z : FiniteRankAtlas 𝕜 X} (hZ : IsZero Z)
    (A : FiniteRankAtlas 𝕜 X) :
    (whitneyZeroLeftIsoOfIsZero hZ A).hom = whitneySnd Z A := (rfl)

@[simp]
theorem whitneyZeroLeftIsoOfIsZero_inv {Z : FiniteRankAtlas 𝕜 X} (hZ : IsZero Z)
    (A : FiniteRankAtlas 𝕜 X) :
    (whitneyZeroLeftIsoOfIsZero hZ A).inv = whitneyInr Z A := (rfl)

@[reassoc]
theorem whitneyMap_zeroLeftIsoOfIsZero_hom {Z Z' A A' : FiniteRankAtlas 𝕜 X}
    (hZ : IsZero Z) (hZ' : IsZero Z') (g : Z ⟶ Z') (f : A ⟶ A') :
    whitneyMap g f ≫ (whitneyZeroLeftIsoOfIsZero hZ' A').hom =
      (whitneyZeroLeftIsoOfIsZero hZ A).hom ≫ f := by
  simp only [whitneyZeroLeftIsoOfIsZero_hom, whitneyMap_snd]

/-- Left unit isomorphism for Whitney sum with the trivial rank-zero atlas. -/
def whitneyZeroLeftIso (A : FiniteRankAtlas 𝕜 X) :
    whitneySum (trivial 𝕜 (0 : LocallyConstant X ℕ)) A ≅ A :=
  whitneyZeroLeftIsoOfIsZero isZero_trivial_zero A

@[simp]
theorem whitneyZeroLeftIso_hom (A : FiniteRankAtlas 𝕜 X) :
    (whitneyZeroLeftIso A).hom = whitneySnd (trivial 𝕜 0) A :=
  whitneyZeroLeftIsoOfIsZero_hom isZero_trivial_zero A

@[simp]
theorem whitneyZeroLeftIso_inv (A : FiniteRankAtlas 𝕜 X) :
    (whitneyZeroLeftIso A).inv = whitneyInr (trivial 𝕜 0) A :=
  whitneyZeroLeftIsoOfIsZero_inv isZero_trivial_zero A

@[reassoc]
theorem whitneyMap_zeroLeftIso_hom {A A' : FiniteRankAtlas 𝕜 X}
    (g : trivial 𝕜 (0 : LocallyConstant X ℕ) ⟶ trivial 𝕜 0) (f : A ⟶ A') :
    whitneyMap g f ≫ (whitneyZeroLeftIso A').hom = (whitneyZeroLeftIso A).hom ≫ f :=
  whitneyMap_zeroLeftIsoOfIsZero_hom isZero_trivial_zero isZero_trivial_zero g f

/-- Right unit isomorphism for Whitney sum with any zero bundle atlas. -/
def whitneyZeroRightIsoOfIsZero (A : FiniteRankAtlas 𝕜 X) {Z : FiniteRankAtlas 𝕜 X}
    (hZ : IsZero Z) : whitneySum A Z ≅ A where
  hom := whitneyFst A Z
  inv := whitneyInl A Z
  hom_inv_id := whitneySum_hom_ext' (by simp) (hZ.eq_of_src _ _)
  inv_hom_id := whitneyInl_fst A Z

@[simp]
theorem whitneyZeroRightIsoOfIsZero_hom (A : FiniteRankAtlas 𝕜 X) {Z : FiniteRankAtlas 𝕜 X}
    (hZ : IsZero Z) :
    (whitneyZeroRightIsoOfIsZero A hZ).hom = whitneyFst A Z := (rfl)

@[simp]
theorem whitneyZeroRightIsoOfIsZero_inv (A : FiniteRankAtlas 𝕜 X) {Z : FiniteRankAtlas 𝕜 X}
    (hZ : IsZero Z) :
    (whitneyZeroRightIsoOfIsZero A hZ).inv = whitneyInl A Z := (rfl)

@[reassoc]
theorem whitneyMap_zeroRightIsoOfIsZero_hom {A A' Z Z' : FiniteRankAtlas 𝕜 X}
    (f : A ⟶ A') (hZ : IsZero Z) (hZ' : IsZero Z') (g : Z ⟶ Z') :
    whitneyMap f g ≫ (whitneyZeroRightIsoOfIsZero A' hZ').hom =
      (whitneyZeroRightIsoOfIsZero A hZ).hom ≫ f := by
  simp only [whitneyZeroRightIsoOfIsZero_hom, whitneyMap_fst]

/-- Right unit isomorphism for Whitney sum with the trivial rank-zero atlas. -/
def whitneyZeroRightIso (A : FiniteRankAtlas 𝕜 X) :
    whitneySum A (trivial 𝕜 (0 : LocallyConstant X ℕ)) ≅ A :=
  whitneyZeroRightIsoOfIsZero A isZero_trivial_zero

@[simp]
theorem whitneyZeroRightIso_hom (A : FiniteRankAtlas 𝕜 X) :
    (whitneyZeroRightIso A).hom = whitneyFst A (trivial 𝕜 0) :=
  whitneyZeroRightIsoOfIsZero_hom A isZero_trivial_zero

@[simp]
theorem whitneyZeroRightIso_inv (A : FiniteRankAtlas 𝕜 X) :
    (whitneyZeroRightIso A).inv = whitneyInl A (trivial 𝕜 0) :=
  whitneyZeroRightIsoOfIsZero_inv A isZero_trivial_zero

@[reassoc]
theorem whitneyMap_zeroRightIso_hom {A A' : FiniteRankAtlas 𝕜 X}
    (f : A ⟶ A') (g : trivial 𝕜 (0 : LocallyConstant X ℕ) ⟶ trivial 𝕜 0) :
    whitneyMap f g ≫ (whitneyZeroRightIso A').hom = (whitneyZeroRightIso A).hom ≫ f :=
  whitneyMap_zeroRightIsoOfIsZero_hom f isZero_trivial_zero isZero_trivial_zero g

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

/-- The trivial atlas of rank `r + s` is isomorphic, by the identity on every coordinate fibre, to
the Whitney sum of the trivial atlases of ranks `r` and `s`. -/
def trivialAddIso (r s : LocallyConstant X ℕ) :
    trivial 𝕜 (r + s) ≅ whitneySum (trivial 𝕜 r) (trivial 𝕜 s) :=
  isoMk (fun x => LinearEquiv.refl 𝕜 (Fin (r x + s x) → 𝕜))
    (continuous_trivialAdd_toFun r s)
    (continuous_trivialAdd_invFun r s)

@[simp]
theorem fiberMap_trivialAddIso_hom (r s : LocallyConstant X ℕ) (x : X) :
    (trivialAddIso (𝕜 := 𝕜) r s).hom.fiberMap x = LinearMap.id :=
  fiberMap_isoMk_hom _ _ _ x

@[simp]
theorem fiberMap_trivialAddIso_inv (r s : LocallyConstant X ℕ) (x : X) :
    (trivialAddIso (𝕜 := 𝕜) r s).inv.fiberMap x = LinearMap.id :=
  fiberMap_isoMk_inv _ _ _ x

end Coherence

end TauCeti.FiniteRankAtlas
