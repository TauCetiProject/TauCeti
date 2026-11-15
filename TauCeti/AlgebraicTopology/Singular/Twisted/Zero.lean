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

The relations come from the boundary of a path: the singular `1`-simplex of a path `γ` from `x`
to `y`, carrying a coefficient `m` at `x`, has boundary `m` transported along `γ` at `y` minus `m`
at `x` (`TauCeti.LocalCoefficientSystem.d_ιTwistedChainComplex_simplex₁_apply`).

## Main definitions

* `TauCeti.LocalCoefficientSystem.ιTwistedHomology₀`: the class in zeroth homology of a
  coefficient in the fibre at a point, with `ιTwistedHomology₀_def` its defining equation.
* `TauCeti.LocalCoefficientSystem.d_ιTwistedChainComplex_simplex₁_apply`: the twisted boundary
  of the singular `1`-simplex of a path.
* `TauCeti.LocalCoefficientSystem.isColimitTwistedHomology₀Cocone`,
  `TauCeti.LocalCoefficientSystem.twistedHomology₀IsoColimit`: zeroth homology is the colimit of the
  local system.

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

/-- The class of a coefficient in the fibre at `x` is the image in zeroth homology of the summand
of the point simplex at `x`.  This is the defining equation of `ιTwistedHomology₀`. -/
theorem ιTwistedHomology₀_def (x : X) :
    ιTwistedHomology₀ L x =
      ιTwistedChainComplex L 0 (ULift.up (TopCat.ofHom (ContinuousMap.const _ x))) ≫
        (twistedChainComplex L).pOpcycles 0 ≫ (twistedChainComplex L).isoHomologyι₀.inv :=
  (rfl)

/-- The class of a coefficient `v` in the fibre at `x` is the image in zeroth homology of the
chain `v` on the zero-simplex `TopCat.toSSetObj₀Equiv.symm x`, which is the point simplex at `x`
used to define `ιTwistedHomology₀`. -/
private lemma ιTwistedHomology₀_apply (x : X) (v : L.obj (FundamentalGroupoid.mk x)) :
    (ιTwistedHomology₀ L x).hom v = (twistedChainComplex L).isoHomologyι₀.inv.hom
      (((twistedChainComplex L).pOpcycles 0).hom
        ((ιTwistedChainComplex L 0 (TopCat.toSSetObj₀Equiv.symm x)).hom v)) :=
  (rfl)

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

/-- The initial vertex of the singular `1`-simplex of a path is the start of the path. -/
lemma initialVertex_simplex₁ {x y : X} (γ : Path x y) :
    initialVertex (simplex₁ γ.toContinuousMap) = FundamentalGroupoid.mk x := by
  rw [initialVertex_eq]
  exact congrArg FundamentalGroupoid.mk ((source₁_simplex₁ γ.toContinuousMap).trans γ.source)

/-- A chain supported on a singular zero-simplex with vertex `x` is supported on the point simplex
at `x`, with the same coefficient up to the identification of the fibres. -/
lemma ιTwistedChainComplex_zero_apply_eq_toSSetObj₀Equiv_symm (σ : (TopCat.toSSet.obj X) _⦋0⦌)
    {x : X} (h : TopCat.toSSetObj₀Equiv σ = x) (c : L.obj (initialVertex σ)) :
    (ιTwistedChainComplex L 0 σ).hom c =
      (ιTwistedChainComplex L 0 (TopCat.toSSetObj₀Equiv.symm x)).hom
        ((L.map (eqToHom ((initialVertex_zero σ).trans (congrArg FundamentalGroupoid.mk h)))).hom
          c) := by
  have key : ∀ (a b : FundamentalGroupoid X) (p : a = b) (c : L.obj a),
      (L.map (eqToHom p)).hom c ≍ c := by
    rintro a b rfl c
    simp
  exact ιTwistedChainComplex_congr L (Equiv.eq_symm_apply _ |>.2 h) (key _ _ _ c).symm

/-- **The boundary of a path.** The twisted boundary of the singular `1`-simplex of a path `γ`
from `x` to `y`, carrying a coefficient `m` in the fibre at `x`, is `m` transported along `γ` at
the vertex `y` minus `m` at the vertex `x`. -/
lemma d_ιTwistedChainComplex_simplex₁_apply {x y : X} (γ : Path x y)
    (m : L.obj (FundamentalGroupoid.mk x)) :
    ((twistedChainComplex L).d 1 0).hom ((ιTwistedChainComplex L 1 (simplex₁ γ.toContinuousMap)).hom
        ((L.map (eqToHom (initialVertex_simplex₁ γ).symm)).hom m)) =
      (ιTwistedChainComplex L 0 (TopCat.toSSetObj₀Equiv.symm y)).hom
          ((L.map (Path.Homotopic.Quotient.mk γ)).hom m) -
        (ιTwistedChainComplex L 0 (TopCat.toSSetObj₀Equiv.symm x)).hom m := by
  have hs := (source₁_simplex₁ γ.toContinuousMap).trans γ.source
  have ht := (target₁_simplex₁ γ.toContinuousMap).trans γ.target
  have h₀ : TopCat.toSSetObj₀Equiv
      ((TopCat.toSSet.obj X).map (δ 0).op (simplex₁ γ.toContinuousMap)) = y :=
    (toSSetObj₀Equiv_δ_zero _).trans ht
  have h₁ : TopCat.toSSetObj₀Equiv
      ((TopCat.toSSet.obj X).map (δ 1).op (simplex₁ γ.toContinuousMap)) = x :=
    (toSSetObj₀Equiv_δ_one _).trans hs
  -- Combine the endpoint identifications into the casts of the path itself.
  have hp : (path₁ (simplex₁ γ.toContinuousMap)).cast hs.symm ht.symm = γ := by
    ext t
    exact path₁_simplex₁_apply γ.toContinuousMap t
  have he₀ : eqToHom (initialVertex_simplex₁ γ).symm ≫
      edgeTransport (simplex₁ γ.toContinuousMap) 0 ≫
        eqToHom (congrArg FundamentalGroupoid.mk h₀) = Path.Homotopic.Quotient.mk γ := by
    have hpath := (FundamentalGroupoid.conj_eqToHom
      (p := Path.Homotopic.Quotient.mk (path₁ (simplex₁ γ.toContinuousMap))) hs.symm
        ht.symm).trans
      ((Path.Homotopic.Quotient.mk_cast _ _ _).symm.trans
        (congrArg Path.Homotopic.Quotient.mk hp))
    simpa only [edgeTransport_zero, Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
      using hpath
  have he₁ : eqToHom (initialVertex_simplex₁ γ).symm ≫
      edgeTransport (simplex₁ γ.toContinuousMap) 1 ≫
        eqToHom (congrArg FundamentalGroupoid.mk h₁) = 𝟙 _ := by
    rw [edgeTransport_one]
    simp
  simp only [edgeTransport, SimplicialObject.δ, Category.assoc] at he₀ he₁
  have hmap {a b c : FundamentalGroupoid X} (f : a ⟶ b) (g : b ⟶ c) (v : L.obj a) :
      (L.map g).hom ((L.map f).hom v) = (L.map (f ≫ g)).hom v := by
    simp
  -- The coefficients at the two endpoints, transported to the point simplices.
  have hc₀ : (L.map (eqToHom
      ((initialVertex_zero _).trans (congrArg FundamentalGroupoid.mk h₀)))).hom
      ((L.map (vertexTransport (δ 0).op (simplex₁ γ.toContinuousMap))).hom
        ((L.map (eqToHom (initialVertex_simplex₁ γ).symm)).hom m)) =
      (L.map (Path.Homotopic.Quotient.mk γ)).hom m := by
    rw [← eqToHom_trans (initialVertex_zero _) (congrArg FundamentalGroupoid.mk h₀)]
    simp only [hmap, Category.assoc, he₀]
  have hc₁ : (L.map (eqToHom
      ((initialVertex_zero _).trans (congrArg FundamentalGroupoid.mk h₁)))).hom
      ((L.map (vertexTransport (δ 1).op (simplex₁ γ.toContinuousMap))).hom
        ((L.map (eqToHom (initialVertex_simplex₁ γ).symm)).hom m)) = m := by
    rw [← eqToHom_trans (initialVertex_zero _) (congrArg FundamentalGroupoid.mk h₁)]
    simp only [hmap, Category.assoc, he₁, L.map_id, ModuleCat.id_apply]
  rw [d_ιTwistedChainComplex_apply, Fin.sum_univ_two,
    ιTwistedChainComplex_zero_apply_eq_toSSetObj₀Equiv_symm L _ h₀,
    ιTwistedChainComplex_zero_apply_eq_toSSetObj₀Equiv_symm L _ h₁, hc₀, hc₁]
  simp [sub_eq_add_neg]

/-- Parallel transport along a path identifies the corresponding fibre classes in zeroth
homology. -/
@[reassoc (attr := simp)]
lemma map_ιTwistedHomology₀ {x y : FundamentalGroupoid X} (p : x ⟶ y) :
    L.map p ≫ ιTwistedHomology₀ L y.as = ιTwistedHomology₀ L x.as := by
  induction p using Path.Homotopic.Quotient.ind with
  | mk γ =>
    refine ModuleCat.hom_ext (LinearMap.ext fun m ↦ ?_)
    -- The boundary of the path simplex identifies the two endpoint classes.
    have hd (c : (twistedChainComplex L).X 1) :
        ((twistedChainComplex L).pOpcycles 0).hom (((twistedChainComplex L).d 1 0).hom c) = 0 := by
      rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, HomologicalComplex.d_pOpcycles,
        ModuleCat.hom_zero, LinearMap.zero_apply]
    have h := hd ((ιTwistedChainComplex L 1 (simplex₁ γ.toContinuousMap)).hom
      ((L.map (eqToHom (initialVertex_simplex₁ γ).symm)).hom m))
    rw [d_ιTwistedChainComplex_simplex₁_apply, map_sub, sub_eq_zero] at h
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, ιTwistedHomology₀_apply, ιTwistedHomology₀_apply,
      h]

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

/-- A chain supported on the singular `1`-simplex of a path only has nonzero coefficients on
simplices whose image lies in the image of the path. -/
lemma range_simplexMap_subset_range_of_ne_zero_simplex₁ {x y : X} (q : Path x y)
    {σ : (TopCat.toSSet.obj X) _⦋1⦌}
    {a : L.obj (initialVertex (simplex₁ q.toContinuousMap))}
    (hσ : (twistedChainComplexCoeff L σ).hom
      ((ιTwistedChainComplex L 1 (simplex₁ q.toContinuousMap)).hom a) ≠ 0) :
    Set.range (simplexMap σ) ⊆ Set.range q := by
  obtain rfl := eq_of_twistedChainComplexCoeff_ιTwistedChainComplex_ne_zero L hσ
  rintro _ ⟨p, rfl⟩
  -- `simplexMap` evaluates the singular simplex at the unlifted point.
  exact ⟨_, (congr($(toSSetObjEquiv_simplex₁ _) p.down)).symm⟩

/-- A chain supported on the singular vertex at a point of a path only has nonzero coefficients on
simplices whose image lies in the image of the path. -/
lemma range_simplexMap_subset_range_of_ne_zero_vertex {x y : X} (q : Path x y)
    {σ : (TopCat.toSSet.obj X) _⦋0⦌}
    {a : L.obj (initialVertex (TopCat.toSSetObj₀Equiv.symm x))}
    (hσ : (twistedChainComplexCoeff L σ).hom
      ((ιTwistedChainComplex L 0 (TopCat.toSSetObj₀Equiv.symm x)).hom a) ≠ 0) :
    Set.range (simplexMap σ) ⊆ Set.range q := by
  obtain rfl := eq_of_twistedChainComplexCoeff_ιTwistedChainComplex_ne_zero L hσ
  rintro _ ⟨_, rfl⟩
  exact ⟨0, q.source⟩

end TauCeti.LocalCoefficientSystem
