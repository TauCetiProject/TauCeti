/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import TauCeti.KnotTheory.Grid.Homology.Basic
public import TauCeti.KnotTheory.Grid.Stabilization.Comparison

/-!
# The fully blocked stabilization factor

Splitting an `X`-marking doubles the fully blocked homology. The comparison sends a chain to
its center part and the fully blocked `X₂`-homotopy of its off-center part. The latter comparison
is a quasi-isomorphism, and the composite of the connecting map with it is zero after every
variable is set to zero. Thus the stabilized mapping cone compares to the cone of zero, whose
homology is two copies of the original homology.

The equivalence here concerns ungraded vector spaces. Its first summand comes from center
states, whose Maslov and Alexander gradings are both one below the original state; the second
summand comes from the `X₂`-homotopy and has the original gradings. These are the two summands of
the usual stabilization factor `W`, in degrees `(-1,-1)` and `(0,0)`.

## References

* Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.2.
* Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.2.

The comparison reuses the reduced off-center-to-center quasi-isomorphism of
`TauCeti.KnotTheory.Grid.Stabilization.Comparison` and Mathlib's mapping cones.
-/

public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (s : Fin n)

local notation "F" => ZMod 2
local notation "C" => GridChain F n
local notation "N" => StabilizeXOffCenterState G s →₀ F
local notation "G'" => stabilizeX G (Fin.castSucc s) (Fin.castSucc (G.X s)) s
local notation "D" => fullyBlockedDifferential G'
local notation "DI" => G.fullyBlockedDifferential
local notation "P" => LinearMap.constantCoeffReduction (stabilizeXCenterProjection G s F)
local notation "Q" => LinearMap.constantCoeffReduction (stabilizeXOffCenterProjection G s F)
local notation "I" => LinearMap.constantCoeffReduction (stabilizeXCenterInclusion G s F)
local notation "J" => LinearMap.constantCoeffReduction (stabilizeXOffCenterInclusion G s F)
local notation "K" => LinearMap.constantCoeffReduction (stabilizeXConnecting G s F)
local notation "H" => LinearMap.constantCoeffReduction (stabilizeXOffCenterToCenter G s F)
local notation "E" => LinearMap.constantCoeffReduction (stabilizeXOffCenterDifferential G s F)

private theorem reduced_p_i : P ∘ₗ I = LinearMap.id := by
  simpa only [LinearMap.constantCoeffReduction_comp, LinearMap.constantCoeffReduction_id] using
    congrArg LinearMap.constantCoeffReduction
      (LinearMap.ext (f := G.stabilizeXCenterProjection s F ∘ₗ G.stabilizeXCenterInclusion s F)
        (g := LinearMap.id) (G.stabilizeXCenterProjection_inclusion s F))

private theorem reduced_q_j : Q ∘ₗ J = LinearMap.id := by
  simpa only [LinearMap.constantCoeffReduction_comp, LinearMap.constantCoeffReduction_id] using
    congrArg LinearMap.constantCoeffReduction
      (LinearMap.ext (f := G.stabilizeXOffCenterProjection s F ∘ₗ
          G.stabilizeXOffCenterInclusion s F)
        (g := LinearMap.id)
        (G.stabilizeXOffCenterProjection_inclusion s F))

private theorem reduced_p_j : P ∘ₗ J = 0 := by
  simpa only [LinearMap.constantCoeffReduction_comp, LinearMap.constantCoeffReduction_zero] using
    congrArg LinearMap.constantCoeffReduction
      (LinearMap.ext (f := G.stabilizeXCenterProjection s F ∘ₗ G.stabilizeXOffCenterInclusion s F)
        (g := 0) (G.stabilizeXCenterProjection_offCenterInclusion s F))

private theorem reduced_q_i : Q ∘ₗ I = 0 := by
  simpa only [LinearMap.constantCoeffReduction_comp, LinearMap.constantCoeffReduction_zero] using
    congrArg LinearMap.constantCoeffReduction
      (LinearMap.ext (f := G.stabilizeXOffCenterProjection s F ∘ₗ G.stabilizeXCenterInclusion s F)
        (g := 0) (G.stabilizeXOffCenterProjection_centerInclusion s F))

private theorem reduced_decomposition : I ∘ₗ P + J ∘ₗ Q = LinearMap.id := by
  simpa only [LinearMap.constantCoeffReduction_comp, LinearMap.constantCoeffReduction_add,
    LinearMap.constantCoeffReduction_id] using congrArg LinearMap.constantCoeffReduction
      (LinearMap.ext
        (f := G.stabilizeXCenterInclusion s F ∘ₗ G.stabilizeXCenterProjection s F +
          G.stabilizeXOffCenterInclusion s F ∘ₗ G.stabilizeXOffCenterProjection s F)
        (g := LinearMap.id) (G.stabilizeXCenterInclusion_projection_add_offCenter s F))

private theorem reduced_D_i : D ∘ₗ I = I ∘ₗ DI + J ∘ₗ K := by
  simpa only [LinearMap.constantCoeffReduction_comp, LinearMap.constantCoeffReduction_add,
    constantCoeffReduction_unblockedDifferential_eq_fullyBlockedDifferential,
    constantCoeffReduction_stabilizeXCenterDifferential_eq_fullyBlockedDifferential] using
    congrArg LinearMap.constantCoeffReduction
      (G.unblockedDifferential_comp_stabilizeXCenterInclusion s F)

private theorem reduced_D_j : D ∘ₗ J = J ∘ₗ E := by
  simpa only [LinearMap.constantCoeffReduction_comp,
    constantCoeffReduction_unblockedDifferential_eq_fullyBlockedDifferential] using
    congrArg LinearMap.constantCoeffReduction
      (G.unblockedDifferential_comp_stabilizeXOffCenterInclusion s F)

private theorem reduced_h_k : H ∘ₗ K = 0 := by
  simpa using congrArg LinearMap.constantCoeffReduction
    (G.stabilizeXOffCenterToCenter_comp_connecting s F)

private theorem reduced_h_e : H ∘ₗ E = DI ∘ₗ H := by
  simpa only [constantCoeffReduction_stabilizeXCenterDifferential_eq_fullyBlockedDifferential]
    using G.constantCoeffReduction_stabilizeXOffCenterToCenter_comp s F

private theorem reduced_k_d : K ∘ₗ DI = E ∘ₗ K := by
  simpa only [LinearMap.constantCoeffReduction_comp,
    constantCoeffReduction_stabilizeXCenterDifferential_eq_fullyBlockedDifferential] using
    congrArg LinearMap.constantCoeffReduction (G.stabilizeXConnecting_comp_centerDifferential s F)

/-- The fully blocked stabilization comparison: the center part, followed by the
`X₂`-homotopy of the off-center part. The center summand has the `(-1,-1)` shift. -/
noncomputable def fullyBlockedStabilizeXMap : GridChain F (n + 1) →ₗ[F] C × C :=
  (P).prod (H ∘ₗ Q)

/-- The first component of the fully blocked stabilization map is the reduced center projection. -/
@[simp]
theorem fullyBlockedStabilizeXMap_fst (c : GridChain F (n + 1)) :
    (G.fullyBlockedStabilizeXMap s c).1 = P c :=
  (rfl)

/-- The second component is the reduced `X₂`-homotopy of the off-center part. -/
@[simp]
theorem fullyBlockedStabilizeXMap_snd (c : GridChain F (n + 1)) :
    (G.fullyBlockedStabilizeXMap s c).2 = H (Q c) :=
  (rfl)

/-- The fully blocked stabilization comparison intertwines the differentials. -/
theorem fullyBlockedStabilizeXMap_comp_differential :
    G.fullyBlockedStabilizeXMap s ∘ₗ D = ((DI).prodMap DI) ∘ₗ G.fullyBlockedStabilizeXMap s := by
  have hc (c : GridChain F (n + 1)) : I (P c) + J (Q c) = c :=
    LinearMap.congr_fun (G.reduced_decomposition s) c
  have hDi (c : C) : D (I c) = I (DI c) + J (K c) :=
    LinearMap.congr_fun (G.reduced_D_i s) c
  have hDj (c : N) : D (J c) = J (E c) :=
    LinearMap.congr_fun (G.reduced_D_j s) c
  have hpi (c : C) : P (I c) = c := LinearMap.congr_fun (G.reduced_p_i s) c
  have hqj (c : N) : Q (J c) = c := LinearMap.congr_fun (G.reduced_q_j s) c
  have hpj (c : N) : P (J c) = 0 := LinearMap.congr_fun (G.reduced_p_j s) c
  have hqi (c : C) : Q (I c) = 0 := LinearMap.congr_fun (G.reduced_q_i s) c
  have hhk (c : C) : H (K c) = 0 := LinearMap.congr_fun (G.reduced_h_k s) c
  have hhe (c : N) : H (E c) = DI (H c) := LinearMap.congr_fun (G.reduced_h_e s) c
  refine LinearMap.ext fun c => ?_
  rw [LinearMap.comp_apply, ← hc c, map_add, hDi, hDj]
  simp [fullyBlockedStabilizeXMap, hpi, hqj, hpj, hqi, hhk, hhe]

/-! The following concrete one-object presentations keep the coefficient carriers of the
reductions explicit. All comparison components are maps of those actual carriers. -/

private noncomputable abbrev reducedCenterComplex :
    HomologicalComplex (ModuleCat F) (ComplexShape.refl Unit) where
  X _ := ModuleCat.of F C
  d _ _ := ModuleCat.ofHom DI
  d_comp_d' _ _ _ _ _ := ((DI).shortComplex G.fullyBlockedDifferential_comp_self_eq_zero).zero

private noncomputable abbrev reducedOffCenterComplex :
    HomologicalComplex (ModuleCat F) (ComplexShape.refl Unit) where
  X _ := ModuleCat.of F N
  d _ _ := ModuleCat.ofHom E
  d_comp_d' _ _ _ _ _ := ((E).shortComplex
    (G.constantCoeffReduction_stabilizeXOffCenterDifferential_comp_self s F)).zero

private noncomputable abbrev reducedStabilizedComplex :
    HomologicalComplex (ModuleCat F) (ComplexShape.refl Unit) where
  X _ := ModuleCat.of F (GridChain F (n + 1))
  d _ _ := ModuleCat.ofHom D
  d_comp_d' _ _ _ _ _ := ((D).shortComplex (G').fullyBlockedDifferential_comp_self_eq_zero).zero

private theorem prod_d_squared : ((DI).prodMap DI) ∘ₗ ((DI).prodMap DI) = 0 := by
  rw [LinearMap.prodMap_comp, G.fullyBlockedDifferential_comp_self_eq_zero]
  ext <;> simp

private noncomputable abbrev reducedProductComplex :
    HomologicalComplex (ModuleCat F) (ComplexShape.refl Unit) where
  X _ := ModuleCat.of F (C × C)
  d _ _ := ModuleCat.ofHom ((DI).prodMap DI)
  d_comp_d' _ _ _ _ _ := (((DI).prodMap DI).shortComplex G.prod_d_squared).zero

private noncomputable def reducedConnectingHom :
    G.reducedCenterComplex ⟶ G.reducedOffCenterComplex s where
  f _ := ModuleCat.ofHom K
  comm' := by
    rintro ⟨⟩ ⟨⟩ -
    exact congrArg ModuleCat.ofHom (G.reduced_k_d s).symm

private noncomputable def reducedComparisonHom :
    G.reducedOffCenterComplex s ⟶ G.reducedCenterComplex where
  f _ := ModuleCat.ofHom H
  comm' := by
    rintro ⟨⟩ ⟨⟩ -
    exact congrArg ModuleCat.ofHom (G.reduced_h_e s).symm

private instance quasiIso_reducedComparisonHom : QuasiIso (G.reducedComparisonHom s) := by
  rw [quasiIso_iff_bijective_homologyMap]
  have hb (δ : C →ₗ[F] C)
      (hδ : δ = (G.stabilizeXCenterDifferential s F).constantCoeffReduction)
      (hδsq : δ ∘ₗ δ = 0) (hH : H ∘ₗ E = δ ∘ₗ H) :
      Function.Bijective (LinearMap.homologyMap H
        (G.constantCoeffReduction_stabilizeXOffCenterDifferential_comp_self s F) hδsq hH) := by
    subst δ
    exact G.homologyMap_constantCoeffReduction_stabilizeXOffCenterToCenter_bijective s F
  exact hb DI (G.constantCoeffReduction_stabilizeXCenterDifferential_eq_fullyBlockedDifferential
    s).symm G.fullyBlockedDifferential_comp_self_eq_zero (G.reduced_h_e s)

private noncomputable def reducedSplitting :
    (ShortComplex.mk (ModuleCat.ofHom J) (ModuleCat.ofHom P)
      (congrArg ModuleCat.ofHom (G.reduced_p_j s))).Splitting where
  r := ModuleCat.ofHom Q
  s := ModuleCat.ofHom I
  f_r := congrArg ModuleCat.ofHom (G.reduced_q_j s)
  s_g := congrArg ModuleCat.ofHom (G.reduced_p_i s)
  id := by
    have hh : (J) ∘ₗ (Q) + (I) ∘ₗ (P) = LinearMap.id := by
      exact (add_comm _ _).trans (G.reduced_decomposition s)
    exact congrArg ModuleCat.ofHom hh

private noncomputable def reducedConeIso :
    G.reducedStabilizedComplex s ≅ homotopyCofiber (G.reducedConnectingHom s) :=
  (homotopyCofiber.isoOfSplitting (G.reducedConnectingHom s) (G.reducedSplitting s)
    (by
      refine ModuleCat.hom_ext (LinearMap.ext fun c => ?_)
      have hneg (u : GridChain F (n + 1)) : -u = u := by
        rw [← neg_one_smul F, CharTwo.neg_eq, one_smul]
      simpa only [reducedSplitting, reducedConnectingHom, ModuleCat.hom_comp,
        ModuleCat.hom_ofHom, ModuleCat.hom_sub, ModuleCat.hom_add, ModuleCat.hom_neg,
        LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply,
        sub_eq_add_neg, hneg] using
        (LinearMap.congr_fun (G.reduced_D_i s) c).trans (add_comm _ _))
    (congrArg ModuleCat.ofHom (G.reduced_D_j s))).symm

private theorem reducedConeIso_hom_f :
    (G.reducedConeIso s).hom.f () =
      ModuleCat.ofHom P ≫
        homotopyCofiber.inlX (G.reducedConnectingHom s) () () (ComplexShape.refl_rel ()) +
      ModuleCat.ofHom Q ≫ homotopyCofiber.inrX (G.reducedConnectingHom s) () :=
  homotopyCofiber.isoOfSplitting_inv_f _ _ _ _

private noncomputable def reducedProductSplitting :
    (ShortComplex.mk (ModuleCat.ofHom (LinearMap.inr F C C))
      (ModuleCat.ofHom (LinearMap.fst F C C)) (by ext c; simp)).Splitting where
  r := ModuleCat.ofHom (LinearMap.snd F C C)
  s := ModuleCat.ofHom (LinearMap.inl F C C)
  f_r := by ext c; simp
  s_g := by ext c; simp
  id := by
    refine ModuleCat.hom_ext (LinearMap.ext fun c => ?_)
    simp

private noncomputable def reducedZeroConeIso :
    homotopyCofiber (0 : G.reducedCenterComplex ⟶ G.reducedCenterComplex) ≅
      G.reducedProductComplex :=
  homotopyCofiber.isoOfSplitting 0 (reducedProductSplitting (n := n))
    (by
      refine ModuleCat.hom_ext (LinearMap.ext fun c => ?_)
      have hneg (u : C) : -u = u := by
        rw [← neg_one_smul F, CharTwo.neg_eq, one_smul]
      simp [reducedProductSplitting, hneg])
    (by
      refine ModuleCat.hom_ext (LinearMap.ext fun c => ?_)
      simp)

private theorem reducedZeroConeIso_hom_f :
    G.reducedZeroConeIso.hom.f () =
      homotopyCofiber.fstX (0 : G.reducedCenterComplex ⟶ G.reducedCenterComplex)
          () () (ComplexShape.refl_rel ()) ≫ ModuleCat.ofHom (LinearMap.inl F C C) +
      homotopyCofiber.sndX (0 : G.reducedCenterComplex ⟶ G.reducedCenterComplex) () ≫
        ModuleCat.ofHom (LinearMap.inr F C C) :=
  homotopyCofiber.isoOfSplitting_hom_f _ _ _ _

private noncomputable def reducedArrowHom :
    Arrow.mk (G.reducedConnectingHom s) ⟶
      Arrow.mk (0 : G.reducedCenterComplex ⟶ G.reducedCenterComplex) :=
  Arrow.homMk' (𝟙 _) (G.reducedComparisonHom s) (by
    refine HomologicalComplex.hom_ext _ _ fun _ => ?_
    simpa only [reducedConnectingHom, reducedComparisonHom, HomologicalComplex.comp_f,
      HomologicalComplex.id_f, HomologicalComplex.zero_f, Category.id_comp,
      ModuleCat.ofHom_zero, ModuleCat.ofHom_comp] using
      congrArg ModuleCat.ofHom (G.reduced_h_k s).symm)

private noncomputable def reducedConeMap :
    homotopyCofiber (G.reducedConnectingHom s) ⟶
      homotopyCofiber (0 : G.reducedCenterComplex ⟶ G.reducedCenterComplex) :=
  homotopyCofiber.mapArrowHom _ _ (fun x => ⟨x, ComplexShape.refl_rel x⟩)
    (G.reducedArrowHom s)

private theorem reducedConeMap_f :
    (G.reducedConeMap s).f () =
      homotopyCofiber.fstX (G.reducedConnectingHom s) () () (ComplexShape.refl_rel ()) ≫
        homotopyCofiber.inlX (0 : G.reducedCenterComplex ⟶ G.reducedCenterComplex)
          () () (ComplexShape.refl_rel ()) +
      homotopyCofiber.sndX (G.reducedConnectingHom s) () ≫ ModuleCat.ofHom H ≫
        homotopyCofiber.inrX (0 : G.reducedCenterComplex ⟶ G.reducedCenterComplex) () := by
  apply homotopyCofiber.ext_from_X (G.reducedConnectingHom s)
    () () (ComplexShape.refl_rel ()) <;>
    simp [reducedConeMap, reducedArrowHom, reducedComparisonHom]

private instance quasiIso_reducedConeMap : QuasiIso (G.reducedConeMap s) := by
  have : QuasiIso (G.reducedArrowHom s).left := inferInstanceAs (QuasiIso (𝟙 _))
  have : QuasiIso (G.reducedArrowHom s).right :=
    inferInstanceAs (QuasiIso (G.reducedComparisonHom s))
  exact homotopyCofiber.quasiIso_mapArrowHom _ _ _ _

private noncomputable def reducedStabilizationHom :
    G.reducedStabilizedComplex s ⟶ G.reducedProductComplex where
  f _ := ModuleCat.ofHom (G.fullyBlockedStabilizeXMap s)
  comm' := by
    rintro ⟨⟩ ⟨⟩ -
    exact congrArg ModuleCat.ofHom (G.fullyBlockedStabilizeXMap_comp_differential s).symm

private theorem reducedStabilizationHom_eq :
    G.reducedStabilizationHom s =
      (G.reducedConeIso s).hom ≫ G.reducedConeMap s ≫ G.reducedZeroConeIso.hom := by
  refine HomologicalComplex.hom_ext _ _ fun x => ?_
  cases x
  ext c <;>
    simp [reducedStabilizationHom, reducedConeIso_hom_f, reducedConeMap_f,
      reducedZeroConeIso_hom_f, Preadditive.add_comp, Preadditive.comp_add, Category.assoc,
      fullyBlockedStabilizeXMap]

private instance quasiIso_reducedStabilizationHom : QuasiIso (G.reducedStabilizationHom s) := by
  rw [G.reducedStabilizationHom_eq s]
  infer_instance

private theorem fullyBlockedStabilizeXMap_homologyMap_bijective :
    Function.Bijective (LinearMap.homologyMap (G.fullyBlockedStabilizeXMap s)
      (G').fullyBlockedDifferential_comp_self_eq_zero G.prod_d_squared
      (G.fullyBlockedStabilizeXMap_comp_differential s)) := by
  simpa only [reducedStabilizationHom, ModuleCat.hom_ofHom] using
    (quasiIso_iff_bijective_homologyMap (G.reducedStabilizationHom s)).mp inferInstance

/-- The fully blocked homology of an `X`-split stabilization is two copies of the original
homology. The equivalence is induced by `fullyBlockedStabilizeXMap`; it concerns ungraded
vector spaces. -/
noncomputable def fullyBlockedHomologyStabilizeXEquivProd :
    (G').fullyBlockedHomology ≃ₗ[F] G.fullyBlockedHomology × G.fullyBlockedHomology :=
  (G').fullyBlockedHomologyEquivLinearMapHomology.trans
    ((LinearEquiv.ofBijective
      (LinearMap.homologyMap (G.fullyBlockedStabilizeXMap s)
        (G').fullyBlockedDifferential_comp_self_eq_zero G.prod_d_squared
        (G.fullyBlockedStabilizeXMap_comp_differential s))
      (G.fullyBlockedStabilizeXMap_homologyMap_bijective s)).trans
      (((DI).homologyProdEquiv DI G.fullyBlockedDifferential_comp_self_eq_zero
        G.fullyBlockedDifferential_comp_self_eq_zero).trans
        (G.fullyBlockedHomologyEquivLinearMapHomology.symm.prodCongr
          G.fullyBlockedHomologyEquivLinearMapHomology.symm)))

/-- The stabilization comparison takes cycles to pairs of cycles. -/
noncomputable def fullyBlockedStabilizeXCycles :
    (G').fullyBlockedCycles →ₗ[F] G.fullyBlockedCycles × G.fullyBlockedCycles := by
  let f := G.fullyBlockedStabilizeXMap s
  have hz (z : (G').fullyBlockedCycles) : (DI).prodMap DI (f z) = 0 := by
    have hDz : D z = 0 := by
      exact LinearMap.mem_ker.mp ((G').fullyBlockedCycles_eq_ker ▸ z.2)
    have hh := LinearMap.congr_fun (G.fullyBlockedStabilizeXMap_comp_differential s) z
    simpa only [LinearMap.comp_apply, hDz, map_zero] using hh.symm
  refine (G.fullyBlockedCycles.prodEquiv G.fullyBlockedCycles).toLinearMap.comp
    ((f.comp (G').fullyBlockedCycles.subtype).codRestrict _ fun z => ?_)
  exact
    ⟨G.fullyBlockedCycles_eq_ker.symm ▸
      LinearMap.mem_ker.mpr (congrArg Prod.fst (hz z)),
      G.fullyBlockedCycles_eq_ker.symm ▸
        LinearMap.mem_ker.mpr (congrArg Prod.snd (hz z))⟩

/-- The first cycle representative is the center part of the stabilized cycle. -/
@[simp]
theorem fullyBlockedStabilizeXCycles_fst (z : (G').fullyBlockedCycles) :
    ((G.fullyBlockedStabilizeXCycles s z).1 : C) = P z := by
  dsimp only [fullyBlockedStabilizeXCycles]
  rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, Submodule.prodEquiv_apply]
  dsimp only
  -- Matching the restriction witness needs product membership to unfold.
  erw [LinearMap.codRestrict_apply (G.fullyBlockedCycles.prod G.fullyBlockedCycles)
    (G.fullyBlockedStabilizeXMap s ∘ₗ (G').fullyBlockedCycles.subtype)]
  exact G.fullyBlockedStabilizeXMap_fst s z

/-- The second cycle representative is the reduced `X₂`-homotopy of its off-center part. -/
@[simp]
theorem fullyBlockedStabilizeXCycles_snd (z : (G').fullyBlockedCycles) :
    ((G.fullyBlockedStabilizeXCycles s z).2 : C) = H (Q z) := by
  dsimp only [fullyBlockedStabilizeXCycles]
  rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, Submodule.prodEquiv_apply]
  dsimp only
  -- Matching the restriction witness needs product membership to unfold.
  erw [LinearMap.codRestrict_apply (G.fullyBlockedCycles.prod G.fullyBlockedCycles)
    (G.fullyBlockedStabilizeXMap s ∘ₗ (G').fullyBlockedCycles.subtype)]
  exact G.fullyBlockedStabilizeXMap_snd s z

/-- The stabilization equivalence sends the class of a cycle to the classes of the two
specified comparison cycles. -/
@[simp]
theorem fullyBlockedHomologyStabilizeXEquivProd_mk (z : (G').fullyBlockedCycles) :
    G.fullyBlockedHomologyStabilizeXEquivProd s (Submodule.Quotient.mk z) =
      (Submodule.Quotient.mk (G.fullyBlockedStabilizeXCycles s z).1,
        Submodule.Quotient.mk (G.fullyBlockedStabilizeXCycles s z).2) := by
  simp only [fullyBlockedHomologyStabilizeXEquivProd, LinearEquiv.trans_apply,
    fullyBlockedHomologyEquivLinearMapHomology_mk, LinearEquiv.ofBijective_apply,
    LinearMap.homologyMap_mk, LinearMap.homologyProdEquiv_mk, LinearEquiv.prodCongr_apply,
    fullyBlockedHomologyEquivLinearMapHomology_symm_mk]
  congr 1

/-- An `X`-split stabilization doubles the fully blocked homology dimension. -/
theorem finrank_fullyBlockedHomology_stabilizeX :
    Module.finrank F (G').fullyBlockedHomology =
      2 * Module.finrank F G.fullyBlockedHomology := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [(G.fullyBlockedHomologyStabilizeXEquivProd s).finrank_eq, Module.finrank_prod]
  omega

end TauCeti.GridDiagram
