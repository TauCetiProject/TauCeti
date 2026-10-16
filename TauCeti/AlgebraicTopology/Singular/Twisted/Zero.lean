/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.TopAdj

/-!
# Zeroth singular homology with local coefficients

The zeroth homology of a local system is its colimit over the fundamental groupoid.
Its generators are the fibres at points, and its relations identify a coefficient with its
parallel transport along a path. This describes degree-zero classes without choosing paths
or basepoints, including for disconnected spaces.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.H.
-/

public section

noncomputable section

open CategoryTheory Limits SimplexCategory Simplicial Convexity

universe u v w

namespace TauCeti.LocalCoefficientSystem

open TauCeti.TopCat

variable {R : Type u} [Ring R] {X : TopCat.{v}}
  (L : LocalCoefficientSystem.{u, v, max v w} R X)

/-- The class in twisted zeroth homology of a coefficient in the fibre at `x`. -/
def ιTwistedHomology₀ (x : X) : L.obj (FundamentalGroupoid.mk x) ⟶ twistedHomology L 0 :=
  ιTwistedChainComplex L 0 (ULift.up (TopCat.ofHom (ContinuousMap.const _ x))) ≫
    (twistedChainComplex L).pOpcycles 0 ≫ (twistedChainComplex L).isoHomologyι₀.inv

/-- A zero-simplex represents the class of its coefficient in the fibre at its vertex. -/
@[reassoc]
lemma ιTwistedChainComplex_pOpcycles_zero (σ : (TopCat.toSSet.obj X) _⦋0⦌) :
    ιTwistedChainComplex L 0 σ ≫ (twistedChainComplex L).pOpcycles 0 ≫
        (twistedChainComplex L).isoHomologyι₀.inv =
      L.map (eqToHom (initialVertex_zero σ)) ≫
        ιTwistedHomology₀ L (TopCat.toSSetObj₀Equiv σ) := by
  obtain ⟨x, rfl⟩ := TopCat.toSSetObj₀Equiv.symm.surjective σ
  -- On the constant simplex the source-fibre equality is definitional.
  unfold ιTwistedHomology₀
  erw [L.map_id]
  rfl

/-- Fibre classes generate twisted zeroth homology. -/
@[ext]
lemma twistedHomology₀_hom_ext {M : ModuleCat.{max v w} R}
    {f g : twistedHomology L 0 ⟶ M}
    (h : ∀ x, ιTwistedHomology₀ L x ≫ f = ιTwistedHomology₀ L x ≫ g) : f = g := by
  apply (cancel_epi ((twistedChainComplex L).isoHomologyι₀.inv)).1
  apply (cancel_epi ((twistedChainComplex L).pOpcycles 0)).1
  apply twistedChainComplex_hom_ext
  intro σ
  simp only [ιTwistedChainComplex_pOpcycles_zero_assoc, h]

private def edgeTransport (σ : (TopCat.toSSet.obj X) _⦋1⦌) (i : Fin 2) :
    initialVertex σ ⟶ FundamentalGroupoid.mk
      (TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj X).δ i σ)) :=
  vertexTransport (δ i).op σ ≫ eqToHom (initialVertex_zero _)

private lemma edgeTransport_eq_path (σ : (TopCat.toSSet.obj X) _⦋1⦌) (i : Fin 2)
    (q : Path (toTopInitialVertex ⦋1⦌)
      (toTop.map (δ i) (toTopInitialVertex ⦋0⦌))) :
    edgeTransport σ i =
      Path.Homotopic.Quotient.mk ((q.map (TopCat.simplexMap σ).continuous).cast rfl
        (by
          rw [TopCat.toSSetObj₀Equiv_apply]
          exact congrArg (X.toSSetObjEquiv _ ((TopCat.toSSet.obj X).δ i σ))
            (Subsingleton.elim _ _))) := by
  rw [edgeTransport]
  erw [vertexTransport_eq_mk (δ i).op σ q]
  have ht : TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj X).δ i σ) =
      TopCat.simplexMap σ (toTop.map (δ i) (toTopInitialVertex ⦋0⦌)) := by
    rw [TopCat.toSSetObj₀Equiv_apply]
    exact congrArg (X.toSSetObjEquiv _ ((TopCat.toSSet.obj X).δ i σ))
      (Subsingleton.elim _ _)
  -- The equality at the last vertex is the target cast in the path class.
  convert (by
    simpa only [eqToHom_refl, Category.id_comp] using
      (FundamentalGroupoid.conj_eqToHom
        (p := Path.Homotopic.Quotient.mk (q.map (TopCat.simplexMap σ).continuous)) rfl ht).trans
        (Path.Homotopic.Quotient.mk_cast (q.map (TopCat.simplexMap σ).continuous) rfl ht).symm)
    using 1
  rfl

private def simplexEdge : Path (toTopInitialVertex ⦋1⦌)
    (toTop.{v}.map (δ (0 : Fin 2)) (toTopInitialVertex ⦋0⦌)) where
  toFun t := ULift.up (StdSimplex.homeomorphI.symm t)
  continuous_toFun := by fun_prop
  source' := by apply ULift.ext; simp
  target' := by
    apply ULift.ext
    erw [toTop_map_toTopInitialVertex_down]
    simp
    rfl

private def simplexStart : Path (toTopInitialVertex ⦋1⦌)
    (toTop.{v}.map (δ (1 : Fin 2)) (toTopInitialVertex ⦋0⦌)) :=
  (Path.refl (toTopInitialVertex ⦋1⦌)).cast rfl (by
    apply ULift.ext
    erw [toTop_map_toTopInitialVertex_down, toTopInitialVertex_down]
    rfl)

/-- The two faces of a singular edge define the same homology class after transport from
its initial vertex. -/
private lemma edgeTransport_ιTwistedHomology₀ (σ : (TopCat.toSSet.obj X) _⦋1⦌) :
    L.map (edgeTransport σ 0) ≫
        ιTwistedHomology₀ L (TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj X).δ 0 σ)) =
      L.map (edgeTransport σ 1) ≫
        ιTwistedHomology₀ L (TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj X).δ 1 σ)) := by
  have h := congrArg (ιTwistedChainComplex L 1 σ ≫ ·)
    ((twistedChainComplex L).d_pOpcycles 1 0)
  simp only [← Category.assoc, ιTwistedChainComplex_d] at h
  have h' := congrArg (· ≫ (twistedChainComplex L).isoHomologyι₀.inv) h
  simpa [Preadditive.add_comp, Preadditive.zsmul_comp, Category.assoc,
    ιTwistedChainComplex_pOpcycles_zero, ← sub_eq_add_neg, sub_eq_zero, edgeTransport,
    L.map_comp, SimplicialObject.δ] using h'

private lemma edgeTransport_one (σ : (TopCat.toSSet.obj X) _⦋1⦌) :
    edgeTransport σ 1 = eqToHom (by
      rw [initialVertex_eq, toSSetObj₀Equiv_δ_one]) := by
  rw [edgeTransport_eq_path σ 1 simplexStart]
  have hs : (initialVertex σ).as =
      TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj X).δ 1 σ) := by
    rw [toSSetObj₀Equiv_δ_one]
    exact congrArg FundamentalGroupoid.as (initialVertex_eq σ)
  rw [FundamentalGroupoid.eqToHom_eq hs, ← Path.Homotopic.Quotient.mk_refl,
    ← Path.Homotopic.Quotient.mk_cast]
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  -- Endpoint casts leave the underlying constant path unchanged; reading its value crosses
  -- the `Path` and continuous-map coercions which the rewrite lemmas leave wrapped.
  change TopCat.simplexMap σ (toTopInitialVertex ⦋1⦌) =
    TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj X).δ 1 σ)
  exact (congrArg FundamentalGroupoid.as (initialVertex_eq σ)).trans
    (toSSetObj₀Equiv_δ_one σ).symm

private lemma edgeTransport_zero (σ : (TopCat.toSSet.obj X) _⦋1⦌) :
    edgeTransport σ 0 =
      eqToHom (initialVertex_eq σ) ≫ Path.Homotopic.Quotient.mk (path₁ σ) ≫
        eqToHom (congrArg FundamentalGroupoid.mk (toSSetObj₀Equiv_δ_zero σ).symm) := by
  rw [edgeTransport_eq_path σ 0 simplexEdge]
  rw [FundamentalGroupoid.conj_eqToHom (congrArg FundamentalGroupoid.as (initialVertex_eq σ))
    (toSSetObj₀Equiv_δ_zero σ)]
  rw [← Path.Homotopic.Quotient.mk_cast]
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rw [Path.cast_coe, Path.cast_coe, Path.map_coe, Function.comp_apply, path₁_apply]
  rfl

/-- Parallel transport along a path identifies the corresponding fibre classes in zeroth
homology. -/
@[reassoc (attr := simp)]
lemma map_ιTwistedHomology₀ {x y : FundamentalGroupoid X} (p : x ⟶ y) :
    L.map p ≫ ιTwistedHomology₀ L y.as = ιTwistedHomology₀ L x.as := by
  induction p using Path.Homotopic.Quotient.ind with
  | mk γ =>
    let σ := simplex₁ γ.toContinuousMap
    have hs : initialVertex σ = x := by
      rw [initialVertex_eq]
      exact congrArg FundamentalGroupoid.mk
        ((source₁_simplex₁ γ.toContinuousMap).trans γ.source)
    have h₀ : TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj X).δ 0 σ) = y.as :=
      (toSSetObj₀Equiv_δ_zero σ).trans ((target₁_simplex₁ γ.toContinuousMap).trans γ.target)
    have h₁ : TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj X).δ 1 σ) = x.as :=
      (toSSetObj₀Equiv_δ_one σ).trans ((source₁_simplex₁ γ.toContinuousMap).trans γ.source)
    -- Combine the endpoint identifications into the casts of the path itself.
    have hp : (path₁ σ).cast
        ((source₁_simplex₁ γ.toContinuousMap).trans γ.source).symm
        ((target₁_simplex₁ γ.toContinuousMap).trans γ.target).symm = γ := by
      ext t
      exact path₁_simplex₁_apply γ.toContinuousMap t
    have he : eqToHom hs.symm ≫ edgeTransport σ 0 ≫
        eqToHom (congrArg FundamentalGroupoid.mk h₀) = Path.Homotopic.Quotient.mk γ := by
      have hpath := (FundamentalGroupoid.conj_eqToHom
        (p := Path.Homotopic.Quotient.mk (path₁ σ))
        ((source₁_simplex₁ γ.toContinuousMap).trans γ.source).symm
        ((target₁_simplex₁ γ.toContinuousMap).trans γ.target).symm).trans
        ((Path.Homotopic.Quotient.mk_cast _ _ _).symm.trans
          (congrArg Path.Homotopic.Quotient.mk hp))
      simpa only [edgeTransport_zero, Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
        using hpath
    have he' : eqToHom hs.symm ≫ edgeTransport σ 1 ≫
        eqToHom (congrArg FundamentalGroupoid.mk h₁) = 𝟙 x := by
      rw [edgeTransport_one]
      simp
    have h' := congrArg (L.map (eqToHom hs.symm) ≫ ·)
      (edgeTransport_ιTwistedHomology₀ L σ)
    have hz₀ : ιTwistedHomology₀ L
        (TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj X).δ 0 σ)) =
        L.map (eqToHom (congrArg FundamentalGroupoid.mk h₀)) ≫ ιTwistedHomology₀ L y.as := by
      simpa only [eqToHom_map, eqToHom_refl, Category.comp_id] using
        eqToHom_naturality (ιTwistedHomology₀ L) h₀
    have hz₁ : ιTwistedHomology₀ L
        (TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj X).δ 1 σ)) =
        L.map (eqToHom (congrArg FundamentalGroupoid.mk h₁)) ≫ ιTwistedHomology₀ L x.as := by
      simpa only [eqToHom_map, eqToHom_refl, Category.comp_id] using
        eqToHom_naturality (ιTwistedHomology₀ L) h₁
    simpa only [hz₀, hz₁, ← L.map_comp_assoc, he, he', L.map_id, Category.id_comp] using h'

/-- On a path-connected space, every twisted zeroth-homology class comes from any chosen fibre. -/
instance epi_ιTwistedHomology₀ [PathConnectedSpace X] (x : X) :
    Epi (ιTwistedHomology₀ L x) where
  left_cancellation f g h := by
    apply twistedHomology₀_hom_ext
    intro y
    let p := Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath y x)
    exact (map_ιTwistedHomology₀_assoc L p f).symm.trans
      ((congrArg (L.map p ≫ ·) h).trans (map_ιTwistedHomology₀_assoc L p g))

/-- A morphism of local systems acts on fibre classes by its component at that point. -/
@[reassoc (attr := simp)]
lemma ιTwistedHomology₀_coefficientMap {K : LocalCoefficientSystem.{u, v, max v w} R X}
    (η : L ⟶ K) (x : X) :
    ιTwistedHomology₀ L x ≫ twistedHomologyCoefficientMap η 0 =
      η.app (FundamentalGroupoid.mk x) ≫ ιTwistedHomology₀ K x := by
  rw [ιTwistedHomology₀, ιTwistedHomology₀]
  -- The canonical degree-zero isomorphism identifies homology with opcycles.
  erw [Category.assoc, Category.assoc, ChainComplex.isoHomologyι₀_inv_naturality,
    HomologicalComplex.p_opcyclesMap_assoc,
    ιTwistedChainComplex_twistedChainComplexCoefficientMap_f_assoc]
  rfl

/-- A continuous map carries a point-fibre class to the class at the image point, with
coefficients pulled back along that map. -/
@[reassoc (attr := simp)]
lemma ιTwistedHomology₀_homologyMap {Y : TopCat.{v}} (f : Y ⟶ X) (y : Y) :
    ιTwistedHomology₀ ((pullback f.hom).obj L) y ≫ twistedHomologyMap f L 0 =
      ιTwistedHomology₀ L (f y) := by
  rw [ιTwistedHomology₀, ιTwistedHomology₀]
  -- As for coefficient maps, first pass from homology to opcycles.
  erw [Category.assoc, Category.assoc, ChainComplex.isoHomologyι₀_inv_naturality,
    HomologicalComplex.p_opcyclesMap_assoc,
    ιTwistedChainComplex_twistedChainComplexMap_f_assoc]
  rfl

/-- The canonical cocone from the local system to its twisted zeroth homology. -/
-- The cocone point must compute to twisted homology in the colimit comparison signatures.
@[expose, simps pt ι_app]
def twistedHomology₀Cocone : Cocone L where
  pt := twistedHomology L 0
  ι :=
    { app x := ιTwistedHomology₀ L x.as
      naturality x y p := by
        rw [Functor.const_obj_map]
        exact (map_ιTwistedHomology₀ L p).trans (Category.comp_id _).symm }

private def zeroChainsDesc (s : Cocone L) : (twistedChainComplex L).X 0 ⟶ s.pt :=
  eqToHom (twistedChainComplex_X L 0) ≫ Sigma.desc (fun σ ↦ s.ι.app (initialVertex σ))

private lemma d_zeroChainsDesc (s : Cocone L) :
    (twistedChainComplex L).d 1 0 ≫ zeroChainsDesc L s = 0 := by
  apply twistedChainComplex_hom_ext
  intro σ
  simp [zeroChainsDesc, s.w, ← sub_eq_add_neg]

-- The construction uses Mathlib's opcycles and degree-zero homology isomorphism and the
-- existing alternating-face twisted chain complex.
private def zeroHomologyDesc (s : Cocone L) : twistedHomology L 0 ⟶ s.pt :=
  (twistedChainComplex L).isoHomologyι₀.hom ≫
    (twistedChainComplex L).descOpcycles (zeroChainsDesc L s) 1 (by simp) (d_zeroChainsDesc L s)

@[reassoc]
private lemma ιTwistedHomology₀_zeroHomologyDesc (s : Cocone L) (x : X) :
    ιTwistedHomology₀ L x ≫ zeroHomologyDesc L s = s.ι.app (FundamentalGroupoid.mk x) := by
  rw [ιTwistedHomology₀, zeroHomologyDesc]
  -- The summand's fibre and the degree-zero object agree at default transparency.
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id_assoc,
    HomologicalComplex.p_descOpcycles]
  erw [zeroChainsDesc, ιTwistedChainComplex_eqToHom_assoc, Sigma.ι_comp_desc]
  rfl

/-- **Zeroth homology with local coefficients is the colimit of the local system.**
The structure maps are the classes of the point fibres. -/
def isColimitTwistedHomology₀Cocone : IsColimit (twistedHomology₀Cocone L) where
  desc s := zeroHomologyDesc L s
  fac s x := ιTwistedHomology₀_zeroHomologyDesc L s x.as
  uniq s f hf := by
    apply twistedHomology₀_hom_ext
    intro x
    exact (hf (FundamentalGroupoid.mk x)).trans
      (ιTwistedHomology₀_zeroHomologyDesc L s x).symm

/-- The canonical identification of twisted zeroth homology with the colimit of the
local system over the fundamental groupoid. -/
def twistedHomology₀IsoColimit : twistedHomology L 0 ≅ colimit L :=
  (isColimitTwistedHomology₀Cocone L).coconePointUniqueUpToIso (colimit.isColimit L)

/-- The colimit comparison sends each fibre class to its colimit inclusion. -/
@[reassoc (attr := simp)]
lemma ιTwistedHomology₀_isoColimit_hom (x : FundamentalGroupoid X) :
    ιTwistedHomology₀ L x.as ≫ (twistedHomology₀IsoColimit L).hom = colimit.ι L x :=
  (isColimitTwistedHomology₀Cocone L).comp_coconePointUniqueUpToIso_hom _ x

/-- The inverse colimit comparison recovers the fibre class from the colimit inclusion. -/
@[reassoc (attr := simp)]
lemma colimit_ι_twistedHomology₀IsoColimit_inv (x : FundamentalGroupoid X) :
    colimit.ι L x ≫ (twistedHomology₀IsoColimit L).inv = ιTwistedHomology₀ L x.as :=
  (isColimitTwistedHomology₀Cocone L).comp_coconePointUniqueUpToIso_inv _ x

/-- The colimit identification is natural in the coefficient system. -/
@[reassoc]
lemma twistedHomology₀IsoColimit_hom_naturality
    {K : LocalCoefficientSystem.{u, v, max v w} R X} (η : L ⟶ K) :
    twistedHomologyCoefficientMap η 0 ≫ (twistedHomology₀IsoColimit K).hom =
      (twistedHomology₀IsoColimit L).hom ≫ colim.map η := by
  apply twistedHomology₀_hom_ext
  intro x
  rw [ιTwistedHomology₀_coefficientMap_assoc]
  erw [ιTwistedHomology₀_isoColimit_hom K (FundamentalGroupoid.mk x),
    ιTwistedHomology₀_isoColimit_hom_assoc L (FundamentalGroupoid.mk x)]
  simp

end TauCeti.LocalCoefficientSystem
