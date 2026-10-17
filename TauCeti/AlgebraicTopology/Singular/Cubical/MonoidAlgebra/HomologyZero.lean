/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomologicalComplex.Basic
public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Basic
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Basic
public import TauCeti.AlgebraicTopology.Singular.Reduced
public import TauCeti.Topology.PathSpace.Moore.Comparison.FundamentalGroup
public import Mathlib.Algebra.Ring.TransferInstance
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# Zeroth homology of the Moore loop algebra

Normalized cubical zeroth homology of the Moore loop space is the group algebra of the
fundamental group, over any commutative coefficient ring. The identification uses the existing
cubical/simplicial comparison and Mathlib's singular zeroth-homology computation, rather than a
second classification of boundaries.

The point chain of a Moore loop is sent to the basis element indexed by the inverse of its
fixed-interval homotopy class. This is the multiplicative convention forced by Mathlib's
`FundamentalGroup.mul_def`: categorical multiplication traverses the right factor first.
The Pontryagin product still concatenates loops in traversal order.

The unital Pontryagin algebra structure on `loopHomologyZero` preserves its original module
structure. `loopHomologyZeroAlgEquiv` identifies it with the group algebra, and
`loopHomologyZeroπ_mul` and `loopHomologyZeroπ_one` identify the actual chain product and unit
with the homology operations. The projection `loopZeroChainToGroupAlgebra` of zero chains is
surjective, and its kernel is exactly the boundaries (`loopZeroChainToGroupAlgebra_eq_zero_iff`).
This supplies the algebraic bridge from loop chains to classical
local coefficients. References: W. S. Massey, *Singular Homology Theory*,
Chapter VII; Barraud--Damian--Humilière--Oancea, *Floer homology with DG coefficients*, §2.2,
https://arxiv.org/html/2404.07953v3#S2.SS2.
The formal construction reuses `TopCat.singularHomology₀Iso` and
`ModuleCat.finsuppCoconeIsColimit`.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology Simplicial

universe u

namespace TauCeti

variable (X : Type u) [TopologicalSpace X] (x : X) (R : Type u) [CommRing R]

/-- Cubical homology of the Moore loop space in degree zero, with coefficients in `R`. -/
abbrev loopHomologyZero : ModuleCat R :=
  ((normalizedCubicalChainComplex R).obj (TopCat.of (MooreLoopSpace X x))).homology 0

/-- The identification of cubical `H₀(ΩX; R)` with `R[π₁(X, x)]`. Its convention on generators
is the inverse path class, so it preserves traversal-order Pontryagin multiplication. -/
def loopHomologyZeroIso :
    loopHomologyZero X x R ≅ ModuleCat.of R (MonoidAlgebra R (FundamentalGroup X x)) :=
  (singularCubicalHomologyIso R (TopCat.of (MooreLoopSpace X x)) 0).symm ≪≫
    (TopCat.of (MooreLoopSpace X x)).singularHomology₀Iso (ModuleCat.of R R) ≪≫
    (sigmaConst.obj (ModuleCat.of R R)).mapIso
      (MooreLoopSpace.zerothHomotopyEquivFundamentalGroup x).toIso ≪≫
    IsColimit.coconePointUniqueUpToIso
      (coproductIsCoproduct (fun _ : FundamentalGroup X x ↦ ModuleCat.of R R))
      (ModuleCat.finsuppCoconeIsColimit R R (FundamentalGroup X x)) ≪≫
    (MonoidAlgebra.coeffLinearEquiv R).symm.toModuleIso

/-- The homology class of a normalized cubical zero chain of Moore loops. -/
def loopHomologyZeroπ :
    NormalizedCubicalChain (MooreLoopSpace X x) R 0 →ₗ[R] loopHomologyZero X x R :=
  let K := (normalizedCubicalChainComplex R).obj (TopCat.of (MooreLoopSpace X x))
  (K.cycles₀Iso.inv ≫ K.homologyπ 0).hom

/-- Projection of zero chains to the fundamental-group algebra through actual cubical homology. -/
def loopZeroChainToGroupAlgebra :
    NormalizedCubicalChain (MooreLoopSpace X x) R 0 →ₗ[R]
      MonoidAlgebra R (FundamentalGroup X x) :=
  (loopHomologyZeroIso X x R).hom.hom.comp (loopHomologyZeroπ X x R)

variable {X x R}

/-- The isomorphism on homology agrees with the zero-chain group-algebra projection. -/
@[simp]
theorem loopHomologyZeroIso_hom_π
    (a : NormalizedCubicalChain (MooreLoopSpace X x) R 0) :
    (loopHomologyZeroIso X x R).hom (loopHomologyZeroπ X x R a) =
      loopZeroChainToGroupAlgebra X x R a :=
  (rfl)

/-- Every zeroth homology class is represented by a normalized cubical zero chain. -/
theorem loopHomologyZeroπ_surjective : Function.Surjective (loopHomologyZeroπ X x R) := by
  let K := (normalizedCubicalChainComplex R).obj (TopCat.of (MooreLoopSpace X x))
  exact (ModuleCat.epi_iff_surjective (K.cycles₀Iso.inv ≫ K.homologyπ 0)).mp (by infer_instance)

private theorem loopHomologyZeroπ_compare
    (a : NormalizedCubicalChain (MooreLoopSpace X x) R 0) :
    (singularCubicalHomologyIso R (TopCat.of (MooreLoopSpace X x)) 0).inv
        (loopHomologyZeroπ X x R a) =
      let L := (TopCat.toSSet.obj (TopCat.of (MooreLoopSpace X x))).chainComplex
        (ModuleCat.of R R)
      (L.cycles₀Iso.inv ≫ L.homologyπ 0)
        (((cubicalToSingular R).app (TopCat.of (MooreLoopSpace X x))).f 0 a) := by
  let K := (normalizedCubicalChainComplex R).obj (TopCat.of (MooreLoopSpace X x))
  let L := (TopCat.toSSet.obj (TopCat.of (MooreLoopSpace X x))).chainComplex
        (ModuleCat.of R R)
  let φ : K ⟶ L := (cubicalToSingular R).app (TopCat.of (MooreLoopSpace X x))
  let a' : K.X 0 := a
  rw [singularCubicalHomologyIso_inv, loopHomologyZeroπ]
  -- Name the actual categorical carriers before rewriting compositions: the zero-chain
  -- carrier is presented by the cubical chain-complex functor.
  change (HomologicalComplex.homologyMap φ 0)
      ((K.cycles₀Iso.inv ≫ K.homologyπ 0) a') =
    (L.cycles₀Iso.inv ≫ L.homologyπ 0) (φ.f 0 a')
  rw [← ModuleCat.comp_apply, Category.assoc, HomologicalComplex.homologyπ_naturality,
    ← Category.assoc, ChainComplex.cycles₀Iso_inv_naturality]
  rfl

/-- A zero-dimensional cube of a Moore loop projects to its fundamental-group basis element. -/
@[simp]
theorem loopZeroChainToGroupAlgebra_ofCube (c : SingularCube (MooreLoopSpace X x) 0) :
    loopZeroChainToGroupAlgebra X x R
        (NormalizedCubicalChain.ofCube (MooreLoopSpace X x) R c) =
      MonoidAlgebra.single (MooreLoopSpace.fundamentalGroupHom x (c 0)) 1 := by
  have hc : c = SingularCube.point (c 0) := by
    apply ContinuousMap.ext
    intro t
    rw [SingularCube.point_apply]
    exact congrArg c (Subsingleton.elim t 0)
  rw [hc]
  simp only [SingularCube.point_apply]
  let γ := c 0
  let T := TopCat.of (MooreLoopSpace X x)
  let L := (TopCat.toSSet.obj T).chainComplex (ModuleCat.of R R)
  let σ := (TopCat.toSSetObj₀Equiv (X := T)).symm γ
  -- First compute the singular homology class through the cubical comparison.
  have hv : (TopCat.toSSet.obj T).ιChainComplex (R := ModuleCat.of R R) σ ≫
      L.cycles₀Iso.inv = L.liftCycles
        ((TopCat.toSSet.obj T).ιChainComplex (R := ModuleCat.of R R) σ) 0
        (by simp) (by simp) := by
    apply (cancel_mono (L.iCycles 0)).1
    simp only [Category.assoc, HomologicalComplex.iCyclesIso_inv_hom_id,
      HomologicalComplex.liftCycles_i]
    exact Category.comp_id ((TopCat.toSSet.obj T).ιChainComplex σ)
  have hπ : (T.singularHomology₀Iso (ModuleCat.of R R)).hom
      ((L.cycles₀Iso.inv ≫ L.homologyπ 0) (simplexChain σ 1)) =
      (Sigma.ι (fun _ : ZerothHomotopy T ↦ ModuleCat.of R R) (.mk γ)) 1 := by
    -- Singular homology is the homology of `L`; naming this carrier lets the
    -- categorical composition equations apply to the point-section computation.
    let φ : L.homology 0 ⟶ ∐ (fun _ : ZerothHomotopy T ↦ ModuleCat.of R R) :=
      (T.singularHomology₀Iso (ModuleCat.of R R)).hom
    change φ ((L.cycles₀Iso.inv ≫ L.homologyπ 0) (simplexChain σ 1)) = _
    have vertex := singularHomology₀Section_singularHomology₀Iso_hom
      (X := T) (ModuleCat.of R R) γ
    rw [singularHomology₀Section_def, SSet.ιHomology₀_eq] at vertex
    rw [← hv] at vertex
    change ((TopCat.toSSet.obj T).ιChainComplex σ ≫ L.cycles₀Iso.inv) ≫
      L.homologyπ 0 ≫ φ = _ at vertex
    have h := congrArg (fun f : ModuleCat.of R R ⟶
        ∐ (fun _ : ZerothHomotopy T ↦ ModuleCat.of R R) ↦ f.hom 1) vertex
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
  -- Next reindex the component coproduct by fundamental-group classes and realize it
  -- as finitely supported coefficients, using the coproduct universal property.
  have hg : Sigma.ι (fun _ : ZerothHomotopy T ↦ ModuleCat.of R R) (.mk γ) ≫
      ((sigmaConst.obj (ModuleCat.of R R)).mapIso
        (MooreLoopSpace.zerothHomotopyEquivFundamentalGroup x).toIso).hom =
      Sigma.ι (fun _ : FundamentalGroup X x ↦ ModuleCat.of R R)
        (MooreLoopSpace.fundamentalGroupHom x γ) := by
    simp only [Functor.mapIso_hom, sigmaConst_obj_map, Equiv.toIso_hom_hom_apply,
      Sigma.ι_comp_map']
    exact congrArg (Sigma.ι (fun _ : FundamentalGroup X x ↦ ModuleCat.of R R))
      (MooreLoopSpace.zerothHomotopyEquivFundamentalGroup_mk γ)
  have he := (coproductIsCoproduct
    (fun _ : FundamentalGroup X x ↦ ModuleCat.of R R)).comp_coconePointUniqueUpToIso_hom
      (ModuleCat.finsuppCoconeIsColimit R R (FundamentalGroup X x))
      ⟨MooreLoopSpace.fundamentalGroupHom x γ⟩
  simp only [Cofan.mk_ι_app, ModuleCat.finsuppCocone] at he
  -- Finally evaluate the composite isomorphism on the cube generator.
  simp only [loopZeroChainToGroupAlgebra, LinearMap.comp_apply,
    loopHomologyZeroIso, Iso.trans_hom, Iso.symm_hom, ModuleCat.hom_comp,
    LinearMap.comp_apply]
  rw [loopHomologyZeroπ_compare, cubicalToSingular_app_f_zero_ofCube]
  -- Use the concrete singular complex in the comparison's target; this is the same
  -- carrier as the simplex class, avoiding instance inference through the functor wrapper.
  change (MonoidAlgebra.coeffLinearEquiv R).symm
      ((IsColimit.coconePointUniqueUpToIso
          (coproductIsCoproduct (fun _ : FundamentalGroup X x ↦ ModuleCat.of R R))
          (ModuleCat.finsuppCoconeIsColimit R R (FundamentalGroup X x))).hom
        (((sigmaConst.obj (ModuleCat.of R R)).map
          (MooreLoopSpace.zerothHomotopyEquivFundamentalGroup x).toIso.hom).hom
          ((T.singularHomology₀Iso (ModuleCat.of R R)).hom
            ((L.cycles₀Iso.inv ≫ L.homologyπ 0) (simplexChain σ 1))))) = _
  rw [hπ]
  have hg' := congrArg (fun f ↦ f.hom 1) hg
  simp only [Functor.mapIso_hom, ModuleCat.hom_comp, LinearMap.comp_apply] at hg'
  rw [hg']
  have he' := congrArg (fun f : ModuleCat.of R R ⟶
      ModuleCat.of R (FundamentalGroup X x →₀ R) ↦ f.hom (1 : R)) he
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    Finsupp.lsingle_apply] at he'
  exact congrArg (MonoidAlgebra.coeffLinearEquiv R).symm he'

/-- Boundaries of one chains vanish under the canonical homology projection. -/
@[simp]
theorem loopHomologyZeroπ_boundary
    (a : NormalizedCubicalChain (MooreLoopSpace X x) R 1) :
    loopHomologyZeroπ X x R
      (NormalizedCubicalChain.boundary (MooreLoopSpace X x) R 0 a) = 0 := by
  let K := (normalizedCubicalChainComplex R).obj (TopCat.of (MooreLoopSpace X x))
  have h : K.d 1 0 ≫ K.cycles₀Iso.inv ≫ K.homologyπ 0 = 0 := by
    rw [← K.toCycles_i 1 0]
    simp only [Category.assoc, HomologicalComplex.iCyclesIso_hom_inv_id_assoc,
      HomologicalComplex.toCycles_comp_homologyπ]
  let a' : K.X 1 := a
  have ha := congrArg (fun f ↦ f.hom a') h
  -- The boundary is the differential of the actual normalized-cubical complex.
  change (K.cycles₀Iso.inv ≫ K.homologyπ 0) (K.d 1 0 a') = 0
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] using ha

/-- The group-algebra projection annihilates cubical boundaries. -/
@[simp]
theorem loopZeroChainToGroupAlgebra_boundary
    (a : NormalizedCubicalChain (MooreLoopSpace X x) R 1) :
    loopZeroChainToGroupAlgebra X x R
      (NormalizedCubicalChain.boundary (MooreLoopSpace X x) R 0 a) = 0 := by
  simp [loopZeroChainToGroupAlgebra, loopHomologyZeroπ_boundary]

/-- **A zero chain of Moore loops has zero homology class exactly when it is a boundary.** -/
theorem loopHomologyZeroπ_eq_zero_iff (a : NormalizedCubicalChain (MooreLoopSpace X x) R 0) :
    loopHomologyZeroπ X x R a = 0 ↔
      a ∈ LinearMap.range (NormalizedCubicalChain.boundary (MooreLoopSpace X x) R 0) := by
  let K := (normalizedCubicalChainComplex R).obj (TopCat.of (MooreLoopSpace X x))
  refine ⟨fun ha ↦ ?_, fun ⟨b, hb⟩ ↦ hb ▸ loopHomologyZeroπ_boundary b⟩
  -- The zero chains are the degree-zero objects of the cubical chain complex.
  let a' : K.X 0 := a
  obtain ⟨b, hb⟩ :=
    (K.moduleCat_homologyπ_eq_zero_iff (m := 1) (by simp) (K.cycles₀Iso.inv a')).1 ha
  refine ⟨b, ?_⟩
  have h : (K.toCycles 1 0 ≫ K.iCycles 0) b = (K.cycles₀Iso.inv ≫ K.iCycles 0) a' := by
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply]
    exact congrArg (K.iCycles 0) hb
  rw [HomologicalComplex.toCycles_i, HomologicalComplex.iCyclesIso_inv_hom_id] at h
  exact h

/-- **A zero chain of Moore loops lies in the kernel of the projection to the group algebra exactly
when it is a boundary.** -/
theorem loopZeroChainToGroupAlgebra_eq_zero_iff
    (a : NormalizedCubicalChain (MooreLoopSpace X x) R 0) :
    loopZeroChainToGroupAlgebra X x R a = 0 ↔
      a ∈ LinearMap.range (NormalizedCubicalChain.boundary (MooreLoopSpace X x) R 0) := by
  rw [← loopHomologyZeroπ_eq_zero_iff, ← loopHomologyZeroIso_hom_π]
  exact (loopHomologyZeroIso X x R).toLinearEquiv.map_eq_zero_iff

/-- The projection of zero chains of Moore loops to the group algebra is surjective. -/
theorem loopZeroChainToGroupAlgebra_surjective :
    Function.Surjective (loopZeroChainToGroupAlgebra X x R) :=
  (loopHomologyZeroIso X x R).toLinearEquiv.surjective.comp loopHomologyZeroπ_surjective

/-- Projection to the group algebra preserves the Pontryagin product of arbitrary zero chains.
Thus the linear identification on actual homology identifies its induced product with the
convolution product in the group algebra. -/
@[simp]
theorem loopZeroChainToGroupAlgebra_mul
    (a b : NormalizedCubicalChain (MooreLoopSpace X x) R 0) :
    loopZeroChainToGroupAlgebra X x R
        (NormalizedCubicalChain.mul (MooreLoopSpace X x) R 0 0 a b) =
      loopZeroChainToGroupAlgebra X x R a * loopZeroChainToGroupAlgebra X x R b := by
  let p := loopZeroChainToGroupAlgebra X x R
  have h : (NormalizedCubicalChain.mul (MooreLoopSpace X x) R 0 0).compr₂ p =
      (LinearMap.mul R (MonoidAlgebra R (FundamentalGroup X x))).compl₁₂ p p := by
    apply NormalizedCubicalChain.linearMap_ext
    intro c
    apply NormalizedCubicalChain.linearMap_ext
    intro d
    have h0 : ((mulMap (MooreLoopSpace X x)).comp (SingularCube.crossProduct c d)) 0 =
        c 0 * d 0 := by
      rw [ContinuousMap.comp_apply, SingularCube.crossProduct_apply, mulMap_apply]
      rfl
    simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, p,
      NormalizedCubicalChain.mul_ofCube, loopZeroChainToGroupAlgebra_ofCube,
      LinearMap.mul_apply_apply]
    have hp := loopZeroChainToGroupAlgebra_ofCube
      ((mulMap (MooreLoopSpace X x)).comp (SingularCube.crossProduct c d)) (R := R)
    rw [hp, h0, map_mul, MonoidAlgebra.single_mul_single, mul_one]
  exact congrArg (fun f ↦ f a b) h

/-- Projection takes the constant, duration-zero loop unit to the group-algebra unit. -/
@[simp]
theorem loopZeroChainToGroupAlgebra_one :
    loopZeroChainToGroupAlgebra X x R (NormalizedCubicalChain.one (MooreLoopSpace X x) R) = 1 := by
  rw [NormalizedCubicalChain.one_def, loopZeroChainToGroupAlgebra_ofCube,
    SingularCube.point_apply, map_one]
  rfl

variable (X x R)

/-- The unital Pontryagin ring on actual cubical zeroth homology. Only multiplication, the unit,
and their powers and casts are transported through the linear comparison; the existing
homology addition, negation and scalar action are preserved. The equations
`loopHomologyZeroπ_mul` and `loopHomologyZeroπ_one` identify this structure with the product
and unit induced by Moore-loop chains, rather than an independently chosen ring structure. -/
instance loopHomologyZeroRing : Ring (loopHomologyZero X x R) := by
  let e := (loopHomologyZeroIso X x R).toLinearEquiv
  letI : Mul (loopHomologyZero X x R) := e.toEquiv.mul
  letI : One (loopHomologyZero X x R) := e.toEquiv.one
  letI : Pow (loopHomologyZero X x R) ℕ := e.toEquiv.pow ℕ
  letI : NatCast (loopHomologyZero X x R) := ⟨fun n ↦ e.symm n⟩
  letI : IntCast (loopHomologyZero X x R) := ⟨fun n ↦ e.symm n⟩
  exact e.injective.ring e e.map_zero (e.apply_symm_apply 1) e.map_add
    (fun a b ↦ e.apply_symm_apply (e a * e b)) e.map_neg e.map_sub
    (fun n a ↦ map_nsmul e n a) (fun n a ↦ map_zsmul e n a)
    (fun a n ↦ e.apply_symm_apply (e a ^ n))
    (fun n ↦ e.apply_symm_apply n) (fun n ↦ e.apply_symm_apply n)

/-- The Pontryagin algebra uses the original coefficient action on cubical homology. -/
instance loopHomologyZeroAlgebra : Algebra R (loopHomologyZero X x R) := by
  let e := (loopHomologyZeroIso X x R).toLinearEquiv
  have hmul (a b : loopHomologyZero X x R) : e (a * b) = e a * e b :=
    e.apply_symm_apply _
  exact Algebra.ofModule
    (fun r a b ↦ e.injective (by rw [hmul, e.map_smul, e.map_smul, hmul, smul_mul_assoc]))
    (fun r a b ↦ e.injective (by rw [hmul, e.map_smul, e.map_smul, hmul, mul_smul_comm]))

/-- The unital algebra identification `H₀(ΩX; R) ≃ₐ[R] R[π₁(X, x)]`, using inverse path
classes to reconcile traversal-order Pontryagin multiplication with Mathlib's group convention.
Its underlying linear equivalence is exactly `loopHomologyZeroIso`. -/
def loopHomologyZeroAlgEquiv :
    loopHomologyZero X x R ≃ₐ[R] MonoidAlgebra R (FundamentalGroup X x) :=
  AlgEquiv.ofLinearEquiv (loopHomologyZeroIso X x R).toLinearEquiv
    ((loopHomologyZeroIso X x R).toLinearEquiv.apply_symm_apply 1)
    (fun a b ↦ (loopHomologyZeroIso X x R).toLinearEquiv.apply_symm_apply
      ((loopHomologyZeroIso X x R).hom a * (loopHomologyZeroIso X x R).hom b))

variable {X x R}

/-- The algebra equivalence preserves the original linear homology comparison. -/
theorem loopHomologyZeroAlgEquiv_apply (a : loopHomologyZero X x R) :
    loopHomologyZeroAlgEquiv X x R a = (loopHomologyZeroIso X x R).hom a := by
  rfl

/-- The algebra equivalence agrees with the existing zero-chain projection. -/
@[simp]
theorem loopHomologyZeroAlgEquiv_π
    (a : NormalizedCubicalChain (MooreLoopSpace X x) R 0) :
    loopHomologyZeroAlgEquiv X x R (loopHomologyZeroπ X x R a) =
      loopZeroChainToGroupAlgebra X x R a := by
  rfl

/-- The product on homology is represented by the actual Pontryagin product on zero chains.
Surjectivity of `loopHomologyZeroπ` makes this equation characterize the homology product. -/
@[simp]
theorem loopHomologyZeroπ_mul
    (a b : NormalizedCubicalChain (MooreLoopSpace X x) R 0) :
    loopHomologyZeroπ X x R
        (NormalizedCubicalChain.mul (MooreLoopSpace X x) R 0 0 a b) =
      loopHomologyZeroπ X x R a * loopHomologyZeroπ X x R b := by
  apply (loopHomologyZeroAlgEquiv X x R).injective
  rw [map_mul, loopHomologyZeroAlgEquiv_π, loopHomologyZeroAlgEquiv_π,
    loopHomologyZeroAlgEquiv_π, loopZeroChainToGroupAlgebra_mul]

/-- The constant duration-zero Moore loop represents the unit of the homology algebra. -/
@[simp]
theorem loopHomologyZeroπ_one :
    loopHomologyZeroπ X x R (NormalizedCubicalChain.one (MooreLoopSpace X x) R) = 1 := by
  apply (loopHomologyZeroAlgEquiv X x R).injective
  rw [map_one, loopHomologyZeroAlgEquiv_π, loopZeroChainToGroupAlgebra_one]

variable {Y : Type u} [TopologicalSpace Y] {y : Y}

/-- Taking the zeroth homology class of a chain commutes with a based continuous map. -/
@[simp]
theorem loopHomologyZeroπ_map (f : C(X, Y)) (hf : f x = y)
    (a : NormalizedCubicalChain (MooreLoopSpace X x) R 0) :
    loopHomologyZeroπ Y y R
        (NormalizedCubicalChain.map R (MooreLoopSpace.map f hf : C(_, _)) 0 a) =
      HomologicalComplex.homologyMap
        ((normalizedCubicalChainComplex R).map
          (TopCat.ofHom (MooreLoopSpace.map f hf : C(_, _)))) 0
        (loopHomologyZeroπ X x R a) := by
  let K := (normalizedCubicalChainComplex R).obj (TopCat.of (MooreLoopSpace X x))
  let L := (normalizedCubicalChainComplex R).obj (TopCat.of (MooreLoopSpace Y y))
  let φ : K ⟶ L := (normalizedCubicalChainComplex R).map
    (TopCat.ofHom (MooreLoopSpace.map f hf : C(_, _)))
  let a' : K.X 0 := a
  have h : K.cycles₀Iso.inv ≫ K.homologyπ 0 ≫ HomologicalComplex.homologyMap φ 0 =
      φ.f 0 ≫ L.cycles₀Iso.inv ≫ L.homologyπ 0 := by
    rw [HomologicalComplex.homologyπ_naturality, ← Category.assoc,
      ChainComplex.cycles₀Iso_inv_naturality, Category.assoc]
  have h' := congrArg (fun g : K.X 0 ⟶ L.homology 0 ↦ g.hom a') h
  -- Use the actual functor-object carriers when applying categorical composition equations.
  change (L.cycles₀Iso.inv ≫ L.homologyπ 0) (φ.f 0 a') =
    (HomologicalComplex.homologyMap φ 0) ((K.cycles₀Iso.inv ≫ K.homologyπ 0) a')
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h'.symm

/-- The zero-chain projection is natural under based continuous maps. -/
@[simp]
theorem loopZeroChainToGroupAlgebra_map (f : C(X, Y)) (hf : f x = y)
    (a : NormalizedCubicalChain (MooreLoopSpace X x) R 0) :
    loopZeroChainToGroupAlgebra Y y R
        (NormalizedCubicalChain.map R (MooreLoopSpace.map f hf : C(_, _)) 0 a) =
      MonoidAlgebra.mapDomainLinearMap R R (FundamentalGroup.mapOfEq f hf)
        (loopZeroChainToGroupAlgebra X x R a) := by
  have h : (loopZeroChainToGroupAlgebra Y y R).comp
      (NormalizedCubicalChain.map R (MooreLoopSpace.map f hf : C(_, _)) 0) =
      (MonoidAlgebra.mapDomainLinearMap R R (FundamentalGroup.mapOfEq f hf)).comp
        (loopZeroChainToGroupAlgebra X x R) := by
    apply NormalizedCubicalChain.linearMap_ext
    intro c
    simp only [LinearMap.comp_apply, NormalizedCubicalChain.map_ofCube,
      loopZeroChainToGroupAlgebra_ofCube, ContinuousMap.comp_apply,
      MonoidAlgebra.mapDomainLinearMap_single]
    exact congrArg (fun g ↦ MonoidAlgebra.single g (1 : R))
      (MooreLoopSpace.fundamentalGroupHom_map f hf (c 0))
  exact congrArg (fun p ↦ p a) h

/-- The homology identification is natural under based maps: it carries the homology map of
Moore loops to the linear map induced by the fundamental-group map. -/
theorem loopHomologyZeroIso_hom_naturality (f : C(X, Y)) (hf : f x = y) :
    HomologicalComplex.homologyMap
        ((normalizedCubicalChainComplex R).map
          (TopCat.ofHom (MooreLoopSpace.map f hf : C(_, _)))) 0 ≫
        (loopHomologyZeroIso Y y R).hom =
      (loopHomologyZeroIso X x R).hom ≫
        ModuleCat.ofHom
          (MonoidAlgebra.mapDomainLinearMap R R (FundamentalGroup.mapOfEq f hf)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  obtain ⟨c, rfl⟩ := loopHomologyZeroπ_surjective (X := X) (x := x) (R := R) a
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
  rw [← loopHomologyZeroπ_map, loopHomologyZeroIso_hom_π,
    loopHomologyZeroIso_hom_π, loopZeroChainToGroupAlgebra_map]

end TauCeti
