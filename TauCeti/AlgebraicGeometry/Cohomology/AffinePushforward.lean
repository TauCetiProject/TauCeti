/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.PushforwardAcyclic.Linear
public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Affine
public import TauCeti.AlgebraicGeometry.Cohomology.SectionsQuotient.Linear
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import TauCeti.AlgebraicGeometry.Scheme.Opens
public import TauCeti.LinearAlgebra.Submodule.Quotient
import Mathlib.Algebra.Category.Grp.Zero
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Colimits

/-!
# Cohomology comparison through an affine morphism

For a morphism `f : X ⟶ Y` over a ring `R`, zeroth cohomology of `f_* M` is finite
exactly when that of `M` is finite. If `f` is affine and `Y` has a cover by two affine opens, the
same holds in degree one for quasicoherent `M`. Both first cohomology groups are computed by the
same sections on the overlap modulo differences of restrictions. These results allow
cohomological finiteness on the projective line to be transported to finite covers.

For every affine morphism and quasi-coherent module, vanishing of positive higher direct
images gives an all-degree comparison, natural in coefficients and linear over any base ring.
This comparison requires no finite open cover or separation hypothesis.

On a quasi-compact scheme with affine diagonal, every quasi-coherent sheaf embeds into a
quasi-coherent sheaf with vanishing positive cohomology
(`AlgebraicGeometry.Scheme.Modules.exists_mono_isQuasicoherent_subsingleton_cohomology`).
The containing sheaf is a finite direct sum of pushforwards from affine opens; the affine
cohomology comparison gives the vanishing used in dimension shifting.

## References

* R. Hartshorne, *Algebraic Geometry*, III, Proposition 8.1 and Section 4.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

/-- The difference of restrictions for a pushforward is the difference on the preimage opens.
The overlap section types agree because preimages preserve intersections. -/
lemma mayerVietorisSectionsDifferenceLinear_pushforward {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : X.Modules) (U V : Y.Opens) (a : Γ((pushforward f).obj M, U))
    (b : Γ((pushforward f).obj M, V)) :
    mayerVietorisSectionsDifferenceLinear ((pushforward f).obj M) U V (a, b) =
      mayerVietorisSectionsDifferenceLinear M (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) (a, b) := by
  -- Instantiate the preimage formulas explicitly: their pair type is only definitionally
  -- that of the pushforward sections.
  simp only [mayerVietorisSectionsDifferenceLinear_apply M (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) a b,
    mayerVietorisSectionsDifference_apply M (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) a b,
    mayerVietorisSectionsDifferenceLinear_apply, mayerVietorisSectionsDifference_apply]
  -- Pushforward restriction maps are restrictions along preimages of the inclusions.
  rfl

/-- An overlap section has zero boundary for a pushforward exactly when it has zero boundary
on the preimage cover. Pushforward sections over `U ⊓ V` are definitionally sections over
`f ⁻¹ᵁ (U ⊓ V)`, which is definitionally `f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V` by `f.preimage_inf`.
No affineness or acyclicity is needed for this kernel comparison. -/
lemma mayerVietorisBoundaryLinear_pushforward_eq_zero_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : X.Modules) (U V : Y.Opens) (hUV : U ⊔ V = ⊤)
    (s : Γ((pushforward f).obj M, U ⊓ V)) :
    mayerVietorisBoundaryLinear ((pushforward f).obj M) U V hUV s = 0 ↔
      mayerVietorisBoundaryLinear M (f ⁻¹ᵁ U) (f ⁻¹ᵁ V)
        (f.preimage_sup_eq_top hUV) s = 0 := by
  have hpre := f.preimage_sup_eq_top hUV
  have hY := SetLike.ext_iff.mp
    (ker_mayerVietorisBoundaryLinear ((pushforward f).obj M) U V hUV) s
  have hX := SetLike.ext_iff.mp
    (ker_mayerVietorisBoundaryLinear M (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) hpre) s
  refine hY.trans (Iff.trans ?_ hX.symm)
  constructor <;> rintro ⟨⟨a, b⟩, h⟩
  · exact ⟨(a, b), (f.mayerVietorisSectionsDifferenceLinear_pushforward M U V a b).symm.trans h⟩
  · exact ⟨(a, b), (f.mayerVietorisSectionsDifferenceLinear_pushforward M U V a b).trans h⟩

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
  [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of R))]

/-- Zeroth cohomology of a pushforward agrees with that of the original sheaf as a module
over the base ring, with no condition on the morphism. -/
def cohomologyZeroPushforwardBaseLinearEquiv (M : X.Modules) :
    Cohomology ((pushforward f).obj M) 0 ≃ₗ[R] Cohomology M 0 := by
  -- Global sections carry the action through `baseRingToGlobalSections`, which is only
  -- propositionally the action through `baseRingToStructurePresheaf` used by
  -- `pushforwardSectionsBaseLinearEquiv`, so that equivalence cannot be reused at `⊤`.
  let e : Γ((pushforward f).obj M, ⊤) ≃ₗ[R] Γ(M, ⊤) :=
    { toFun := id
      invFun := id
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' r s := by
        rw [base_smul_globalSections_eq_baseRingToStructurePresheaf_smul]
        exact (pushforward_baseRingToStructurePresheaf_smul R f M ⊤ r s).trans
          (base_smul_globalSections_eq_baseRingToStructurePresheaf_smul R X M r s).symm }
  exact (cohomologyZeroBaseLinearEquiv R Y ((pushforward f).obj M)).trans
    (e.trans (cohomologyZeroBaseLinearEquiv R X M).symm)

/-- The degree-zero comparison identifies the same global section on source and target. -/
@[simp]
lemma cohomologyZeroPushforwardBaseLinearEquiv_apply (M : X.Modules)
    (x : Cohomology ((pushforward f).obj M) 0) :
    f.cohomologyZeroPushforwardBaseLinearEquiv (R := R) M x =
      (cohomologyZeroBaseLinearEquiv R X M).symm
        (cohomologyZeroBaseLinearEquiv R Y ((pushforward f).obj M) x) := by
  rfl

/-- The inverse degree-zero comparison identifies the same global section on target and
source. -/
@[simp]
lemma cohomologyZeroPushforwardBaseLinearEquiv_symm_apply (M : X.Modules)
    (x : Cohomology M 0) :
    (f.cohomologyZeroPushforwardBaseLinearEquiv (R := R) M).symm x =
      (cohomologyZeroBaseLinearEquiv R Y ((pushforward f).obj M)).symm
        (cohomologyZeroBaseLinearEquiv R X M x) := by
  rfl

/-- Zeroth cohomology of a pushforward is finite over the base ring exactly when the original
zeroth cohomology is finite, with no condition on the morphism. -/
@[simp]
theorem moduleFinite_cohomology_zero_pushforward_iff (M : X.Modules) :
    Module.Finite R (Cohomology ((pushforward f).obj M) 0) ↔
      Module.Finite R (Cohomology M 0) :=
  Module.Finite.equiv_iff (f.cohomologyZeroPushforwardBaseLinearEquiv (R := R) M)

/-- On a target covered by two affine opens, first cohomology of an affine pushforward agrees with
that on the source as a module over the base ring. -/
def cohomologyOnePushforwardBaseLinearEquiv [IsAffineHom f]
    (M : X.Modules) [M.IsQuasicoherent]
    (U V : Y.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ⊔ V = ⊤) :
    Cohomology ((pushforward f).obj M) 1 ≃ₗ[R] Cohomology M 1 := by
  -- Restrict the two Mayer–Vietoris boundaries to the common scalar ring `R`.
  let N := (pushforward f).obj M
  let : Algebra R Γ(Y, ⊤) := ((Y.baseRingToStructurePresheaf R).app (op ⊤)).hom.toAlgebra
  let : Algebra R Γ(X, ⊤) := ((X.baseRingToStructurePresheaf R).app (op ⊤)).hom.toAlgebra
  let : Module R Γ(N, U ⊓ V) :=
    Module.compHom _ ((Y.baseRingToStructurePresheaf R).app (op (U ⊓ V))).hom
  -- `f.preimage_inf` is `rfl`: the preimage of the overlap and the overlap of preimages
  -- are definitionally equal. The two local instances below present the same scalar action
  -- in each syntactic form, since instance search does not unfold preimages here.
  let : Module R Γ(M, f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V) :=
    Module.compHom _ ((X.baseRingToStructurePresheaf R).app (op (f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V))).hom
  have := isScalarTower_sections R N (U ⊓ V)
  have := isScalarTower_sections R M (f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V)
  have := isScalarTower_cohomology R Y N 1
  have := isScalarTower_cohomology R X M 1
  have hpre := f.preimage_sup_eq_top hUV
  let : Module R Γ(M, f ⁻¹ᵁ (U ⊓ V)) :=
    Module.compHom _ ((X.baseRingToStructurePresheaf R).app (op (f ⁻¹ᵁ (U ⊓ V)))).hom
  let e := pushforwardSectionsBaseLinearEquiv (R := R) f M (U ⊓ V)
  let bY := (mayerVietorisBoundaryLinear N U V hUV).restrictScalars R
  let bX := ((mayerVietorisBoundaryLinear M (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) hpre).restrictScalars R).comp
    e.toLinearMap
  have hbY : Function.Surjective bY := by
    exact mayerVietorisBoundaryLinear_surjective N U V hUV
      (subsingleton_cohomologyOn_succ_of_isAffineOpen N hU 0)
      (subsingleton_cohomologyOn_succ_of_isAffineOpen N hV 0)
  have hbX : Function.Surjective bX := by
    exact (mayerVietorisBoundaryLinear_surjective M _ _ hpre
      (subsingleton_cohomologyOn_succ_of_isAffineOpen M (hU.preimage f) 0)
      (subsingleton_cohomologyOn_succ_of_isAffineOpen M (hV.preimage f) 0)).comp
        e.surjective
  -- The compatibility of restriction differences identifies the two boundary kernels.
  have hker : LinearMap.ker bY = LinearMap.ker bX := by
    ext s
    simp only [LinearMap.mem_ker]
    have he : e s = s := pushforwardSectionsBaseLinearEquiv_apply R f M (U ⊓ V) s
    have hx : bX s = mayerVietorisBoundaryLinear M (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) hpre s := by
      exact congrArg (mayerVietorisBoundaryLinear M (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) hpre) he
    rw [hx]
    exact f.mayerVietorisBoundaryLinear_pushforward_eq_zero_iff M U V hUV s
  -- Both cohomology modules are the quotient of the common overlap by this kernel.
  exact bY.equivOfSurjectiveOfKerEq bX hbY hbX hker

/-- The degree-one comparison carries the boundary of an overlap section to its boundary
on the preimage cover. The section types are identified by pushforward and `f.preimage_inf`. -/
@[simp]
lemma cohomologyOnePushforwardBaseLinearEquiv_boundary [IsAffineHom f]
    (M : X.Modules) [M.IsQuasicoherent]
    (U V : Y.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ⊔ V = ⊤)
    (s : Γ((pushforward f).obj M, U ⊓ V)) :
    dsimp% only [pushforward_obj_obj]
      (f.cohomologyOnePushforwardBaseLinearEquiv (R := R) M U V hU hV hUV
        (mayerVietorisBoundaryLinear ((pushforward f).obj M) U V hUV s)) =
      mayerVietorisBoundaryLinear M (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) (f.preimage_sup_eq_top hUV) s := by
  let : Module R Γ((pushforward f).obj M, U ⊓ V) :=
    Module.compHom _ ((Y.baseRingToStructurePresheaf R).app (op (U ⊓ V))).hom
  let : Module R Γ(M, f ⁻¹ᵁ (U ⊓ V)) :=
    Module.compHom _ ((X.baseRingToStructurePresheaf R).app (op (f ⁻¹ᵁ (U ⊓ V)))).hom
  -- The comparison sends the boundary of `s` to the boundary of its image under the
  -- section comparison, which is `s` itself.
  exact (LinearMap.equivOfSurjectiveOfKerEq_apply _ _ _ _ _ s).trans (congrArg
    (mayerVietorisBoundaryLinear M (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) (f.preimage_sup_eq_top hUV))
    (pushforwardSectionsBaseLinearEquiv_apply R f M (U ⊓ V) s))

/-- The inverse degree-one comparison carries the boundary of a section over the overlap of
the preimage cover to the boundary of the same section on the target cover. -/
@[simp]
lemma cohomologyOnePushforwardBaseLinearEquiv_symm_boundary [IsAffineHom f]
    (M : X.Modules) [M.IsQuasicoherent]
    (U V : Y.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ⊔ V = ⊤)
    (s : Γ(M, f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V)) :
    (f.cohomologyOnePushforwardBaseLinearEquiv (R := R) M U V hU hV hUV).symm
        (mayerVietorisBoundaryLinear M (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) (f.preimage_sup_eq_top hUV) s) =
      mayerVietorisBoundaryLinear ((pushforward f).obj M) U V hUV s :=
  (LinearEquiv.symm_apply_eq _).mpr
    (f.cohomologyOnePushforwardBaseLinearEquiv_boundary M U V hU hV hUV s).symm

/-- On a target covered by two affine opens, first cohomology of an affine pushforward is finite
exactly when first cohomology on the source is finite. -/
theorem moduleFinite_cohomology_one_pushforward_iff_of_two_affine_opens [IsAffineHom f]
    (M : X.Modules) [M.IsQuasicoherent]
    (U V : Y.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ⊔ V = ⊤) :
    Module.Finite R (Cohomology ((pushforward f).obj M) 1) ↔
      Module.Finite R (Cohomology M 1) :=
  Module.Finite.equiv_iff (f.cohomologyOnePushforwardBaseLinearEquiv (R := R) M U V hU hV hUV)

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]

/-- An affine morphism preserves the cohomology of a quasi-coherent coefficient module. -/
def cohomologyPushforwardIsoOfIsAffineHom (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    AddCommGrpCat.of (Cohomology ((pushforward f).obj M) n) ≅
      AddCommGrpCat.of (Cohomology M n) :=
  f.cohomologyPushforwardIsoOfIsZeroHigherDirectImageSucc M
    (f.isZero_higherDirectImage_succ_of_isAffineHom M) n

/-- The affine cohomology comparison is natural in the quasi-coherent coefficient module. -/
@[reassoc]
theorem cohomologyPushforwardIsoOfIsAffineHom_naturality {M N : X.Modules} [M.IsQuasicoherent]
    [N.IsQuasicoherent] (φ : M ⟶ N) (n : ℕ) :
    (cohomologyFunctor Y n).map ((pushforward f).map φ) ≫
        (cohomologyPushforwardIsoOfIsAffineHom f N n).hom =
      (cohomologyPushforwardIsoOfIsAffineHom f M n).hom ≫
        (cohomologyFunctor X n).map φ :=
  f.cohomologyPushforwardIsoOfIsZeroHigherDirectImageSucc_naturality φ
    (f.isZero_higherDirectImage_succ_of_isAffineHom M)
    (f.isZero_higherDirectImage_succ_of_isAffineHom N) n

/-- The affine cohomology comparison intertwines a global function with its pullback. -/
lemma cohomologyPushforwardIsoOfIsAffineHom_hom_smul (M : X.Modules) [M.IsQuasicoherent] (n : ℕ)
    (r : Γ(Y, ⊤)) (x : Cohomology ((pushforward f).obj M) n) :
    (cohomologyPushforwardIsoOfIsAffineHom f M n).hom (r • x) =
      f.appTop r • (cohomologyPushforwardIsoOfIsAffineHom f M n).hom x :=
  f.cohomologyPushforwardIsoOfIsZeroHigherDirectImageSucc_hom_smul M
    (f.isZero_higherDirectImage_succ_of_isAffineHom M) n r x

variable (R : Type u) [CommRing R] [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))]
  [f.IsOver (Spec (.of R))]

/-- An affine morphism over `R` preserves quasi-coherent cohomology as an `R`-module. -/
def cohomologyPushforwardBaseLinearEquivOfIsAffineHom (M : X.Modules) [M.IsQuasicoherent]
    (n : ℕ) : Cohomology ((pushforward f).obj M) n ≃ₗ[R] Cohomology M n :=
  f.cohomologyPushforwardBaseLinearEquivOfIsZeroHigherDirectImageSucc R M
    (f.isZero_higherDirectImage_succ_of_isAffineHom M) n

/-- The linear affine comparison has the forward map of the additive comparison. -/
@[simp]
lemma cohomologyPushforwardBaseLinearEquivOfIsAffineHom_apply (M : X.Modules)
    [M.IsQuasicoherent] (n : ℕ) (x : Cohomology ((pushforward f).obj M) n) :
    cohomologyPushforwardBaseLinearEquivOfIsAffineHom f R M n x =
      (cohomologyPushforwardIsoOfIsAffineHom f M n).hom x :=
  f.cohomologyPushforwardBaseLinearEquivOfIsZeroHigherDirectImageSucc_apply R M
    (f.isZero_higherDirectImage_succ_of_isAffineHom M) n x

/-- The inverse linear affine comparison has the map of the inverse additive comparison. -/
@[simp]
lemma cohomologyPushforwardBaseLinearEquivOfIsAffineHom_symm_apply (M : X.Modules)
    [M.IsQuasicoherent] (n : ℕ) (x : Cohomology M n) :
    (cohomologyPushforwardBaseLinearEquivOfIsAffineHom f R M n).symm x =
      (cohomologyPushforwardIsoOfIsAffineHom f M n).inv x :=
  f.cohomologyPushforwardBaseLinearEquivOfIsZeroHigherDirectImageSucc_symm_apply R M
    (f.isZero_higherDirectImage_succ_of_isAffineHom M) n x

/-- Finiteness of quasi-coherent cohomology transfers through any affine morphism over `R`. -/
theorem moduleFinite_cohomology_pushforward_iff_of_isAffineHom (M : X.Modules)
    [M.IsQuasicoherent] (n : ℕ) :
    Module.Finite R (Cohomology ((pushforward f).obj M) n) ↔
      Module.Finite R (Cohomology M n) :=
  Module.Finite.equiv_iff (cohomologyPushforwardBaseLinearEquivOfIsAffineHom f R M n)

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory Limits TopologicalSpace
open TauCeti TauCeti.AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

open TauCeti.AlgebraicGeometry in
/-- Every quasi-coherent sheaf `M` on a quasi-compact scheme with affine diagonal embeds into a
quasi-coherent sheaf with no cohomology in positive degrees, namely the direct sum of the
pushforwards of the restrictions of `M` to the members of a finite affine open cover. -/
lemma exists_mono_isQuasicoherent_subsingleton_cohomology [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (M : X.Modules) [M.IsQuasicoherent] :
    ∃ (I : X.Modules) (i : M ⟶ I), I.IsQuasicoherent ∧ Mono i ∧
      ∀ k, Subsingleton (Cohomology I (k + 1)) := by
  let 𝒰 := X.affineCover.finiteSubcover
  let U : 𝒰.I₀ → X.Opens := fun i ↦ (𝒰.f i).opensRange
  have hU (i : 𝒰.I₀) : IsAffineOpen (U i) := isAffineOpen_opensRange (𝒰.f i)
  have hcover : ⨆ i, U i = ⊤ := 𝒰.iSup_opensRange
  -- An affine open of a scheme with affine diagonal is an affine morphism.
  have hι (i : 𝒰.I₀) : IsAffineHom (U i).ι := (hU i).isAffineHom_ι
  have : HasFiniteBiproducts X.Modules := .of_hasFiniteProducts
  let F : 𝒰.I₀ → X.Modules := fun i ↦
    (pushforward (U i).ι).obj ((restrictFunctor (U i).ι).obj M)
  have hF (i : 𝒰.I₀) : (F i).IsQuasicoherent := by
    have := isQuasicoherent_restrictFunctor (U i).ι M
    infer_instance
  refine ⟨⨁ F, biproduct.lift fun i ↦ (restrictAdjunction (U i).ι).unit.app M,
    isQuasicoherent_of_isColimit (K := Discrete.functor F) (fun j ↦ hF j.as)
      (biproduct.isColimit F), ⟨fun {T} a b hab ↦ ?_⟩, fun k ↦ ?_⟩
  · -- A section of `M` is determined by its restrictions to the members of the cover.
    ext W t
    refine TopCat.Sheaf.eq_of_locally_eq' (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
      (fun i ↦ (U i).ι ''ᵁ ((U i).ι ⁻¹ᵁ W)) W (fun i ↦ homOfLE ((U i).ι.image_preimage_le W))
      ?_ _ _ fun i ↦ ?_
    · intro x hx
      have hx' : x ∈ ⨆ i, U i := hcover.symm ▸ trivial
      obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx'
      refine Opens.mem_iSup.mpr ⟨i, ?_⟩
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact ⟨hi, hx⟩
    · have := congrArg (fun φ ↦ (φ ≫ biproduct.π F i).app W t) hab
      simp only [Category.assoc, biproduct.lift_π, Scheme.Modules.Hom.comp_app,
        restrictAdjunction_unit_app_app] at this
      exact this
  · -- Each summand has no higher cohomology, being pushed forward from an affine scheme along an
    -- affine morphism; so neither has their direct sum.
    have hzero (i : 𝒰.I₀) : IsZero ((cohomologyFunctor X (k + 1)).obj (F i)) := by
      have : IsAffine (U i).toScheme := hU i
      have := isQuasicoherent_restrictFunctor (U i).ι M
      have : Subsingleton (Cohomology (F i) (k + 1)) :=
        ((U i).ι.cohomologyPushforwardIsoOfIsAffineHom _
          (k + 1)).addCommGroupIsoToAddEquiv.toEquiv.subsingleton_congr.mpr
            (subsingleton_cohomology_succ_of_isAffine _ k)
      exact @AddCommGrpCat.isZero_of_subsingleton _ this
    refine AddCommGrpCat.subsingleton_of_isZero (G := (cohomologyFunctor X (k + 1)).obj (⨁ F)) ?_
    rw [IsZero.iff_id_eq_zero, ← CategoryTheory.Functor.map_id, ← biproduct.total,
      Functor.map_sum]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [CategoryTheory.Functor.map_comp, (hzero i).eq_of_tgt ((cohomologyFunctor X (k + 1)).map
      (biproduct.π F i)) 0, zero_comp]

end AlgebraicGeometry.Scheme.Modules
