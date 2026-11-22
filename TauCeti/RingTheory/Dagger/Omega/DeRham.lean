/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.RingTheory.Dagger.Omega.Kaehler
public import TauCeti.RingTheory.Dagger.Omega.Map
public import TauCeti.RingTheory.Kaehler.ExteriorDerivative

/-!
# The overconvergent de Rham complex and its functoriality

For any commutative `R`-algebra `A` with Noetherian `Omega R A` (in particular any `K`-dagger
algebra), `(Omega.d R A).TwistedExt` is Noetherian over `A`, so `(Omega.d R A).derTwistedExt`
lifts uniquely through `Omega.d R A`, yielding the characteristic-free exterior derivative
`Omega.exteriorDeriv R A q : ⋀[A]^q (Omega R A) →ₗ[R] ⋀[A]^(q + 1) (Omega R A)`, Grosse-Klönne's
overconvergent de Rham complex `Omega.deRhamComplex R A`, and cohomology
`Omega.deRhamCohomology R A q`, functorial in `K`-dagger algebras.

## References

* E. Grosse-Klönne, *Finiteness of de Rham cohomology in rigid analysis*, Duke Math. J. 113
  (2002), §1.2.
* K. Kedlaya, *Finiteness of rigid cohomology with coefficients*, Duke Math. J. 134 (2006), §3.1.
-/

public section
noncomputable section

open CategoryTheory

namespace TauCeti.Dagger.Omega

/-! ### Exterior derivative, de Rham complex, and cohomology -/

section DeRham
variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] [IsNoetherian A (Omega R A)]

/-- **The graded exterior derivative on `ExteriorAlgebra A (Omega R A)`.** -/
def exteriorAlgebraDeriv : ExteriorAlgebra A (Omega R A) →ₗ[R] ExteriorAlgebra A (Omega R A) :=
  (d R A).exteriorAlgebraDeriv (lift (d R A).derTwistedExt) (span_range_d R A)
    (lift_d (d R A).derTwistedExt)

/-- **The `q`-th exterior derivative `⋀[A]^q (Omega R A) →ₗ[R] ⋀[A]^(q + 1) (Omega R A)`.** -/
def exteriorDeriv (q : ℕ) : ⋀[A]^q (Omega R A) →ₗ[R] ⋀[A]^(q + 1) (Omega R A) :=
  (d R A).exteriorDeriv (lift (d R A).derTwistedExt) (span_range_d R A)
    (lift_d (d R A).derTwistedExt) q

section ExteriorDerivLemmas
variable {R A}
@[simp] theorem coe_exteriorDeriv_apply (q : ℕ) (ω : ⋀[A]^q (Omega R A)) :
    (exteriorDeriv R A q ω : ExteriorAlgebra A (Omega R A)) = exteriorAlgebraDeriv R A ω.1 :=
  Derivation.coe_exteriorDeriv_apply _ _ _ _ q ω
@[simp] theorem exteriorAlgebraDeriv_algebraMap (a : A) :
    exteriorAlgebraDeriv R A (algebraMap A (ExteriorAlgebra A (Omega R A)) a) =
      ExteriorAlgebra.ι A (d R A a) := Derivation.exteriorAlgebraDeriv_algebraMap _ _ _ _ a
@[simp] theorem exteriorAlgebraDeriv_ι_apply (a : A) :
    exteriorAlgebraDeriv R A (ExteriorAlgebra.ι A (d R A a)) = 0 :=
  Derivation.exteriorAlgebraDeriv_ι_apply _ _ _ _ a
/-- **Ambient-algebra square-zero identity (`d ∘ d = 0`) on `ExteriorAlgebra A (Omega R A)`**,
for pointwise simplification of inhomogeneous elements. -/
@[simp] theorem exteriorAlgebraDeriv_exteriorAlgebraDeriv (x : ExteriorAlgebra A (Omega R A)) :
    exteriorAlgebraDeriv R A (exteriorAlgebraDeriv R A x) = 0 :=
  Derivation.exteriorAlgebraDeriv_exteriorAlgebraDeriv _ _ _ _ x
/-- Graded Leibniz rule on `ExteriorAlgebra A (Omega R A)` for a left factor in
`⋀[A]^p (Omega R A)`, with sign `(-1) ^ p` determined by the left factor's degree. -/
theorem exteriorAlgebraDeriv_mul_of_mem_exteriorPower {p : ℕ} {x : ExteriorAlgebra A (Omega R A)}
    (hx : x ∈ ⋀[A]^p (Omega R A)) (y : ExteriorAlgebra A (Omega R A)) :
    exteriorAlgebraDeriv R A (x * y) =
      exteriorAlgebraDeriv R A x * y + (-1 : A) ^ p • (x * exteriorAlgebraDeriv R A y) :=
  Derivation.exteriorAlgebraDeriv_mul_of_mem_exteriorPower _ _ _ _ hx y
@[simp] theorem exteriorDeriv_zero_symm (a : A) :
    exteriorDeriv R A 0 ((exteriorPower.zeroEquiv A (Omega R A)).symm a) =
      (exteriorPower.oneEquiv A (Omega R A)).symm (d R A a) :=
  Derivation.exteriorDeriv_zero_symm _ _ _ _ a
theorem oneEquiv_exteriorDeriv_zero (ω : ⋀[A]^0 (Omega R A)) :
    exteriorPower.oneEquiv A (Omega R A) (exteriorDeriv R A 0 ω) =
      d R A (exteriorPower.zeroEquiv A (Omega R A) ω) :=
  Derivation.oneEquiv_exteriorDeriv_zero _ _ _ _ ω
/-- **Pointwise homogeneous square-zero identity** `d (d ω) = 0` for an overconvergent `q`-form
`ω`, used for `simp` rewriting. -/
@[simp] theorem exteriorDeriv_exteriorDeriv_apply (q : ℕ) (ω : ⋀[A]^q (Omega R A)) :
    exteriorDeriv R A (q + 1) (exteriorDeriv R A q ω) = 0 :=
  Derivation.exteriorDeriv_exteriorDeriv_apply _ _ _ _ q ω
/-- **Bundled square-zero composition** `d_{q+1} ∘ₗ d_q = 0` as `R`-linear maps on exterior
powers of `Omega R A`, used to construct `deRhamComplex R A`. -/
theorem exteriorDeriv_comp_exteriorDeriv (q : ℕ) :
    (exteriorDeriv R A (q + 1)) ∘ₗ (exteriorDeriv R A q) = 0 :=
  Derivation.exteriorDeriv_comp_exteriorDeriv _ _ _ _ q
/-- **Scalar Leibniz rule on overconvergent `q`-forms**: `d (a • ω) = d a ∧ ω + a • d ω`. -/
theorem exteriorDeriv_smul (q : ℕ) (a : A) (ω : ⋀[A]^q (Omega R A)) :
    exteriorDeriv R A q (a • ω) =
      TauCeti.ExteriorAlgebra.wedgeLeft (d R A a) q ω + a • exteriorDeriv R A q ω :=
  Derivation.exteriorDeriv_smul _ _ _ _ q a ω
/-- Every wedge product `d b₀ ∧ ⋯ ∧ d b_{q-1}` of exact differentials is closed (`d = 0`). -/
@[simp] theorem exteriorDeriv_ιMulti_comp_d {q : ℕ} (b : Fin q → A) :
    exteriorDeriv R A q (exteriorPower.ιMulti A q (d R A ∘ b)) = 0 :=
  Derivation.exteriorDeriv_ιMulti_comp_D _ _ _ _ b
/-- **Formula on scaled exact-differential wedges**: since `d b₀ ∧ ⋯ ∧ d b_{q-1}` is closed,
only its scalar coefficient `a` is differentiated:
`d (a • (d b₀ ∧ ⋯ ∧ d b_{q-1})) = d a ∧ d b₀ ∧ ⋯ ∧ d b_{q-1}`. -/
theorem exteriorDeriv_smul_ιMulti_comp_d {q : ℕ} (a : A) (b : Fin q → A) :
    exteriorDeriv R A q (a • exteriorPower.ιMulti A q (d R A ∘ b)) =
      exteriorPower.ιMulti A (q + 1) (Fin.cons (d R A a) (d R A ∘ b)) :=
  Derivation.exteriorDeriv_smul_ιMulti_comp_D _ _ _ _ a b
/-- **Graded Leibniz rule for `exteriorPower.wedge`** of a `p`-form and a `q`-form, with sign
`(-1) ^ p` determined by the left factor's degree. -/
theorem exteriorDeriv_wedge (p q : ℕ) (ω : ⋀[A]^p (Omega R A)) (η : ⋀[A]^q (Omega R A)) :
    exteriorDeriv R A (p + q) (exteriorPower.wedge A (Omega R A) p q ω η) =
      LinearEquiv.ofEq _ _ (congrArg (⋀[A]^· (Omega R A)) (Nat.add_right_comm p 1 q))
        (exteriorPower.wedge A (Omega R A) (p + 1) q (exteriorDeriv R A p ω) η) +
        (-1 : A) ^ p • exteriorPower.wedge A (Omega R A) p (q + 1) ω (exteriorDeriv R A q η) :=
  Derivation.exteriorDeriv_wedge _ _ _ _ p q ω η

/-- **Comparison with algebraic Kähler forms**: `ofKaehler` intertwines
`KaehlerDifferential.exteriorDeriv` with `Omega.exteriorDeriv` in every degree. -/
theorem map_ofKaehler_exteriorDeriv (q : ℕ) (ω : ⋀[A]^q Ω[A⁄R]) :
    exteriorPower.map (q + 1) (ofKaehler R A) (KaehlerDifferential.exteriorDeriv R A q ω) =
      exteriorDeriv R A q (exteriorPower.map q (ofKaehler R A) ω) := by
  rw [← exteriorPower.mapSemilinear_eq_map (q + 1), ← exteriorPower.mapSemilinear_eq_map q]
  exact KaehlerDifferential.mapSemilinear_exteriorDeriv_of_derivation _ _ _ _
    (AlgHom.id R A) (ofKaehler R A) (ofKaehler_D R A) q ω

/-- When algebraic Kähler differentials are finite, `(ofKaehlerEquiv R A).exteriorPower`
identifies the algebraic and universally finite exterior derivatives. -/
theorem ofKaehlerEquiv_exteriorDeriv [Module.Finite A Ω[A⁄R]] (q : ℕ) (ω : ⋀[A]^q Ω[A⁄R]) :
    (ofKaehlerEquiv R A).exteriorPower (q + 1) (KaehlerDifferential.exteriorDeriv R A q ω) =
      exteriorDeriv R A q ((ofKaehlerEquiv R A).exteriorPower q ω) := by
  rw [← LinearEquiv.coe_toLinearMap, ← LinearEquiv.coe_toLinearMap,
    LinearEquiv.exteriorPower_toLinearMap, LinearEquiv.exteriorPower_toLinearMap,
    show (ofKaehlerEquiv R A).toLinearMap = ofKaehler R A from
      LinearMap.ext (ofKaehlerEquiv_apply R A)]
  exact map_ofKaehler_exteriorDeriv q ω
end ExteriorDerivLemmas

/-- **The universally finite (overconvergent) de Rham cochain complex**
`0 → ⋀⁰ Ω¹ → ⋀¹ Ω¹ → ⋀² Ω¹ → ⋯` in `ModuleCat R`. -/
def deRhamComplex : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun q ↦ ModuleCat.of R (⋀[A]^q (Omega R A)))
    (fun q ↦ ModuleCat.ofHom (exteriorDeriv R A q))
    (fun q ↦ ModuleCat.hom_ext (exteriorDeriv_comp_exteriorDeriv q))

/-- Canonical identification of `(deRhamComplex R A).X q` with `⋀[A]^q (Omega R A)`. -/
def deRhamComplexXIso (q : ℕ) : (deRhamComplex R A).X q ≅ ModuleCat.of R (⋀[A]^q (Omega R A)) := by
  unfold deRhamComplex; exact Iso.refl _

@[reassoc] theorem deRhamComplex_d (q : ℕ) :
    (deRhamComplex R A).d q (q + 1) ≫ (deRhamComplexXIso R A (q + 1)).hom =
      (deRhamComplexXIso R A q).hom ≫ ModuleCat.ofHom (exteriorDeriv R A q) := by
  dsimp +instances [deRhamComplexXIso, deRhamComplex]; simp
theorem deRhamComplex_d_apply (q : ℕ) (x : (deRhamComplex R A).X q) :
    (deRhamComplex R A).d q (q + 1) x =
      (deRhamComplexXIso R A (q + 1)).inv
        (exteriorDeriv R A q ((deRhamComplexXIso R A q).hom x)) := by
  rw [(Iso.eq_comp_inv _).mpr (deRhamComplex_d R A q), ModuleCat.comp_apply, ModuleCat.comp_apply,
    ConcreteCategory.hom_ofHom]

/-- The `R`-submodule of closed `q`-forms `ker (d : Ω^q → Ω^{q+1})`. -/
def closedForms (q : ℕ) : Submodule R (⋀[A]^q (Omega R A)) := LinearMap.ker (exteriorDeriv R A q)

/-- The `R`-submodule of exact `q`-forms: `⊥` in degree `0` and `range d` in degree `q + 1`. -/
def exactForms : (q : ℕ) → Submodule R (⋀[A]^q (Omega R A))
  | 0 => ⊥
  | q + 1 => LinearMap.range (exteriorDeriv R A q)

@[simp] theorem mem_closedForms {q : ℕ} (ω : ⋀[A]^q (Omega R A)) :
    ω ∈ closedForms R A q ↔ exteriorDeriv R A q ω = 0 := Iff.rfl
@[simp] theorem exactForms_zero : exactForms R A 0 = ⊥ := (rfl)
@[simp] theorem exactForms_succ (q : ℕ) :
    exactForms R A (q + 1) = LinearMap.range (exteriorDeriv R A q) := (rfl)
theorem exactForms_le_closedForms : (q : ℕ) → exactForms R A q ≤ closedForms R A q
  | 0 => by simp
  | q + 1 => LinearMap.range_le_ker_iff.mpr (exteriorDeriv_comp_exteriorDeriv q)
theorem exteriorDeriv_mem_closedForms (q : ℕ) (ω : ⋀[A]^q (Omega R A)) :
    exteriorDeriv R A q ω ∈ closedForms R A (q + 1) :=
  exactForms_le_closedForms R A (q + 1) ⟨ω, rfl⟩

/-- **Overconvergent de Rham cohomology** `H^q_dR(A/R)`. -/
abbrev deRhamCohomology (q : ℕ) : Type _ := (deRhamComplex R A).homology q

theorem deRhamComplex_d_eq_zero_of_mem_closedForms (q : ℕ) {ω : ⋀[A]^q (Omega R A)}
    (hω : ω ∈ closedForms R A q) :
    (deRhamComplex R A).d q (q + 1) ((deRhamComplexXIso R A q).inv ω) = 0 :=
  (HomologicalComplex.moduleCat_d_inv_eq_zero_iff _ _ (deRhamComplex_d R A) ω).mpr hω

namespace deRhamCohomology
/-- The cycle-class map from closed `q`-forms to `deRhamCohomology R A q`. -/
def mk (q : ℕ) : closedForms R A q →ₗ[R] deRhamCohomology R A q :=
  (deRhamComplex R A).moduleCatCohomologyClassOfIso (fun q ↦ ⋀[A]^q (Omega R A))
    (closedForms R A) (deRhamComplexXIso R A)
    (fun _ z ↦ (mem_closedForms R A z).trans
      (HomologicalComplex.moduleCat_d_inv_eq_zero_iff _ _ (deRhamComplex_d R A) z).symm) q

/-- Compatibility of `deRhamCohomology.mk` with `HomologicalComplex.moduleCatHomologyClass`. -/
theorem mk_eq_moduleCatHomologyClass (q : ℕ) :
    mk R A q = (deRhamComplex R A).moduleCatHomologyClass (Z := closedForms R A q)
        (CochainComplex.next ℕ q) ((deRhamComplexXIso R A q).inv.hom ∘ₗ (closedForms R A q).subtype)
        (fun ω ↦ deRhamComplex_d_eq_zero_of_mem_closedForms R A q ω.2) := LinearMap.ext fun _ ↦ by
  rw [mk, HomologicalComplex.moduleCatCohomologyClassOfIso_apply,
    HomologicalComplex.moduleCatHomologyClass_apply]; rfl

/-- Every cohomology class in `deRhamCohomology R A q` has a closed `q`-form representative. -/
theorem mk_surjective (q : ℕ) : Function.Surjective (mk R A q) :=
  (deRhamComplex R A).moduleCatCohomologyClassOfIso_surjective _ _ _ _ q
/-- A closed `q`-form represents zero in `deRhamCohomology R A q` iff it is exact. -/
@[simp] theorem mk_eq_zero_iff (q : ℕ) (ω : closedForms R A q) :
    mk R A q ω = 0 ↔ ω.1 ∈ exactForms R A q :=
  (deRhamComplex R A).moduleCatCohomologyClassOfIso_eq_zero_iff _ _ (exactForms R A) _ _
    (HomologicalComplex.moduleCat_mem_iff_exists_d_eq_inv _ _ _ (deRhamComplex_d R A)
      (exactForms_zero R A) (exactForms_succ R A)) q ω
/-- Two closed `q`-forms represent the same cohomology class iff their difference is exact. -/
theorem mk_eq_iff (q : ℕ) (ω η : closedForms R A q) :
    mk R A q ω = mk R A q η ↔ (ω - η).1 ∈ exactForms R A q := by
  rw [← sub_eq_zero, ← map_sub, mk_eq_zero_iff]
/-- The kernel of `deRhamCohomology.mk R A q` is the restriction of `exactForms R A q` to
`closedForms R A q`, since `mk` is only defined on closed forms. -/
theorem ker_mk (q : ℕ) :
    LinearMap.ker (mk R A q) = (exactForms R A q).comap (closedForms R A q).subtype :=
  Submodule.ext (mk_eq_zero_iff R A q)
/-- In degree `0`, `deRhamCohomology.mk R A 0` is injective since `exactForms R A 0 = ⊥`. -/
theorem mk_zero_injective : Function.Injective (mk R A 0) :=
  (injective_iff_map_eq_zero _).mpr fun _ hω ↦ Subtype.ext <| by simpa [exactForms_zero] using hω

/-- In degree zero, `deRhamCohomology R A 0` is canonically equivalent to `closedForms R A 0`. -/
def zeroEquivClosedForms : closedForms R A 0 ≃ₗ[R] deRhamCohomology R A 0 :=
  LinearEquiv.ofBijective (mk R A 0) ⟨mk_zero_injective R A, mk_surjective R A 0⟩
@[simp] theorem zeroEquivClosedForms_apply (ω : closedForms R A 0) :
    zeroEquivClosedForms R A ω = mk R A 0 ω := (rfl)
end deRhamCohomology

/-- If every closed `q`-form is exact, then `deRhamCohomology R A q` is subsingleton. -/
theorem subsingleton_deRhamCohomology_of_closedForms_le_exactForms {q : ℕ}
    (h : closedForms R A q ≤ exactForms R A q) : Subsingleton (deRhamCohomology R A q) :=
  subsingleton_of_forall_eq 0 fun c ↦
    have ⟨ω, hc⟩ := deRhamCohomology.mk_surjective R A q c
    hc ▸ (deRhamCohomology.mk_eq_zero_iff R A q ω).mpr (h ω.2)

/-- `deRhamComplex R A` is exact in degree `q + 1` iff every closed `(q + 1)`-form is exact. -/
theorem exactAt_deRhamComplex_succ_iff (q : ℕ) :
    (deRhamComplex R A).ExactAt (q + 1) ↔ exactForms R A (q + 1) = closedForms R A (q + 1) := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology, ModuleCat.isZero_iff_subsingleton]
  exact ⟨fun _ ↦ le_antisymm (exactForms_le_closedForms R A (q + 1)) fun ω hω ↦
      (deRhamCohomology.mk_eq_zero_iff R A (q + 1) ⟨ω, hω⟩).mp (Subsingleton.elim _ 0),
    fun h ↦ subsingleton_deRhamCohomology_of_closedForms_le_exactForms R A h.ge⟩

end DeRham

/-! ### Functoriality along homomorphisms of dagger algebras -/

section Functoriality
variable {K A B C : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CommRing A] [CommRing B] [CommRing C] [Algebra K A] [Algebra K B] [Algebra K C]
  [IsDaggerAlgebra K A] [IsDaggerAlgebra K B] [IsDaggerAlgebra K C]

/-- **Naturality of `exteriorDeriv` along a homomorphism of dagger algebras.** -/
theorem mapSemilinear_exteriorDeriv (f : A →ₐ[K] B) (q : ℕ) (ω : ⋀[A]^q (Omega K A)) :
    exteriorPower.mapSemilinear (q + 1) (mapSemilinear f) (exteriorDeriv K A q ω) =
      exteriorDeriv K B q (exteriorPower.mapSemilinear q (mapSemilinear f) ω) :=
  Derivation.mapSemilinear_exteriorDeriv _ _ _ _ _ _ _ _ f (mapSemilinear f) (mapSemilinear_d f) q ω

omit [IsDaggerAlgebra K A] in
/-- The `K`-linear pullback of overconvergent `q`-forms along `f : A →ₐ[K] B`. -/
def formsMap (f : A →ₐ[K] B) (q : ℕ) : ⋀[A]^q (Omega K A) →ₗ[K] ⋀[B]^q (Omega K B) where
  toFun := exteriorPower.mapSemilinear q (mapSemilinear f)
  map_add' := map_add _
  map_smul' r ω := by
    have hfr : f.toRingHom (algebraMap K A r) = algebraMap K B r := f.commutes r
    rw [← algebraMap_smul A r ω, LinearMap.map_smulₛₗ, hfr, algebraMap_smul, RingHom.id_apply]

omit [IsDaggerAlgebra K A] in
@[simp] theorem formsMap_apply (f : A →ₐ[K] B) (q : ℕ) (ω : ⋀[A]^q (Omega K A)) :
    formsMap f q ω = exteriorPower.mapSemilinear q (mapSemilinear f) ω := (rfl)
@[simp] theorem formsMap_id (q : ℕ) : formsMap (AlgHom.id K A) q = LinearMap.id :=
  LinearMap.ext fun ω ↦ (congrArg (exteriorPower.mapSemilinear q · ω) mapSemilinear_id).trans
    (exteriorPower.mapSemilinear_id_apply q ω)
omit [IsDaggerAlgebra K A] in
theorem formsMap_comp (g : B →ₐ[K] C) (f : A →ₐ[K] B) (q : ℕ) :
    formsMap (g.comp f) q = (formsMap g q) ∘ₗ (formsMap f q) := LinearMap.ext fun ω ↦ by
  rw [formsMap_apply, mapSemilinear_comp, exteriorPower.mapSemilinear_comp_apply]; rfl
theorem exteriorDeriv_formsMap (f : A →ₐ[K] B) (q : ℕ) (ω : ⋀[A]^q (Omega K A)) :
    exteriorDeriv K B q (formsMap f q ω) = formsMap f (q + 1) (exteriorDeriv K A q ω) :=
  (mapSemilinear_exteriorDeriv f q ω).symm
theorem exteriorDeriv_comp_formsMap (f : A →ₐ[K] B) (q : ℕ) :
    (exteriorDeriv K B q) ∘ₗ (formsMap f q) = (formsMap f (q + 1)) ∘ₗ (exteriorDeriv K A q) :=
  LinearMap.ext (exteriorDeriv_formsMap f q)

namespace closedForms
/-- Pullback of closed overconvergent `q`-forms along `f : A →ₐ[K] B`. -/
def map (f : A →ₐ[K] B) (q : ℕ) : closedForms K A q →ₗ[K] closedForms K B q :=
  ((formsMap f q).domRestrict (closedForms K A q)).codRestrict (closedForms K B q) fun ω ↦ by
    rw [mem_closedForms, LinearMap.domRestrict_apply, exteriorDeriv_formsMap,
      (mem_closedForms K A ω.1).mp ω.2, map_zero]
@[simp] theorem coe_map (f : A →ₐ[K] B) (q : ℕ) (ω : closedForms K A q) :
    (map f q ω).1 = formsMap f q ω.1 := (rfl)
@[simp] theorem map_id (q : ℕ) : map (AlgHom.id K A) q = LinearMap.id :=
  LinearMap.ext fun _ ↦ Subtype.ext (by simp)
theorem map_comp (g : B →ₐ[K] C) (f : A →ₐ[K] B) (q : ℕ) :
    map (g.comp f) q = (map g q) ∘ₗ (map f q) :=
  LinearMap.ext fun _ ↦ Subtype.ext (by simp [formsMap_comp])
theorem map_mem_exactForms (f : A →ₐ[K] B) : ∀ (q : ℕ) (ω : closedForms K A q),
    ω.1 ∈ exactForms K A q → (map f q ω).1 ∈ exactForms K B q
  | 0, ω, hω => by rw [exactForms_zero, Submodule.mem_bot] at hω ⊢; rw [coe_map, hω, map_zero]
  | q + 1, _, ⟨η, hη⟩ => ⟨formsMap f q η, by rw [exteriorDeriv_formsMap, hη]; rfl⟩
end closedForms

namespace deRhamCohomology
/-- Covariant functoriality of `deRhamCohomology` along `f : A →ₐ[K] B`. -/
def map (f : A →ₐ[K] B) (q : ℕ) : deRhamCohomology K A q →ₗ[K] deRhamCohomology K B q :=
  (LinearMap.liftOfSurjective (R := K) (M := closedForms K A q) (M₂ := deRhamCohomology K A q)
    (M₃ := deRhamCohomology K B q) (f := mk K A q) (mk_surjective K A q))
    ⟨(mk K B q).comp (closedForms.map f q), fun ω hω ↦ by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, mk_eq_zero_iff]
      exact closedForms.map_mem_exactForms f q ω ((mk_eq_zero_iff K A q ω).mp hω)⟩
@[simp] theorem map_mk (f : A →ₐ[K] B) (q : ℕ) (ω : closedForms K A q) :
    map f q (mk K A q ω) = mk K B q (closedForms.map f q ω) := by
  rw [map, LinearMap.equivOfSurjective_apply]; rfl
@[simp] theorem map_id (q : ℕ) : map (AlgHom.id K A) q = LinearMap.id :=
  LinearMap.ext fun c ↦ by obtain ⟨ω, rfl⟩ := mk_surjective K A q c; simp
theorem map_comp (g : B →ₐ[K] C) (f : A →ₐ[K] B) (q : ℕ) :
    map (g.comp f) q = (map g q).comp (map f q) := LinearMap.ext fun c ↦ by
  obtain ⟨ω, rfl⟩ := mk_surjective K A q c; simp [closedForms.map_comp]

/-- An equivalence of `K`-dagger algebras induces a `K`-linear equivalence on de Rham cohomology. -/
def equivOfAlgEquiv (e : A ≃ₐ[K] B) (q : ℕ) : deRhamCohomology K A q ≃ₗ[K] deRhamCohomology K B q :=
  LinearEquiv.ofLinearMap (map e.toAlgHom q) (map e.symm.toAlgHom q)
    (by rw [← map_comp, AlgEquiv.comp_symm, map_id])
    (by rw [← map_comp, AlgEquiv.symm_comp, map_id])
@[simp] theorem equivOfAlgEquiv_apply (e : A ≃ₐ[K] B) (q : ℕ) (c : deRhamCohomology K A q) :
    equivOfAlgEquiv e q c = map e.toAlgHom q c := (rfl)
@[simp] theorem equivOfAlgEquiv_symm_apply (e : A ≃ₐ[K] B) (q : ℕ) (c : deRhamCohomology K B q) :
    (equivOfAlgEquiv e q).symm c = map e.symm.toAlgHom q c := (rfl)
end deRhamCohomology
end Functoriality

section ComplexFunctoriality
universe u v
variable {K : Type u} {A B C : Type v} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CommRing A] [CommRing B] [CommRing C] [Algebra K A] [Algebra K B] [Algebra K C]
  [IsDaggerAlgebra K A] [IsDaggerAlgebra K B] [IsDaggerAlgebra K C]

namespace deRhamComplex
/-- The cochain map `deRhamComplex K A ⟶ deRhamComplex K B` induced by `f : A →ₐ[K] B`. -/
def map (f : A →ₐ[K] B) : deRhamComplex K A ⟶ deRhamComplex K B :=
  CochainComplex.ofHom
    (fun q ↦ (deRhamComplexXIso K A q).hom ≫ ModuleCat.ofHom (formsMap f q) ≫
      (deRhamComplexXIso K B q).inv) fun q ↦ by
      have hcomm : ModuleCat.ofHom (formsMap f q) ≫ ModuleCat.ofHom (exteriorDeriv K B q) =
          ModuleCat.ofHom (exteriorDeriv K A q) ≫ ModuleCat.ofHom (formsMap f (q + 1)) :=
        ModuleCat.hom_ext (exteriorDeriv_comp_formsMap f q)
      rw [(Iso.eq_comp_inv _).mpr (deRhamComplex_d K A q),
        (Iso.eq_comp_inv _).mpr (deRhamComplex_d K B q)]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hcomm]

@[reassoc] theorem map_f (f : A →ₐ[K] B) (q : ℕ) :
    (map f).f q ≫ (deRhamComplexXIso K B q).hom =
      (deRhamComplexXIso K A q).hom ≫ ModuleCat.ofHom (formsMap f q) := by simp [map]
@[simp] theorem map_id : map (AlgHom.id K A) = 𝟙 _ := by ext q : 2; simp [map]
theorem map_comp (g : B →ₐ[K] C) (f : A →ₐ[K] B) : map (g.comp f) = map f ≫ map g := by
  ext q : 2; simp [map, formsMap_comp g f q]

/-- The map induced on cohomology by `deRhamComplex.map f` is `deRhamCohomology.map f`. -/
theorem homologyMap_map (f : A →ₐ[K] B) (q : ℕ) :
    HomologicalComplex.homologyMap (map f) q = ModuleCat.ofHom (deRhamCohomology.map f q) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun c ↦ ?_)
  obtain ⟨ω, rfl⟩ := deRhamCohomology.mk_surjective K A q c
  rw [ModuleCat.hom_ofHom, deRhamCohomology.map_mk, deRhamCohomology.mk, deRhamCohomology.mk,
    HomologicalComplex.moduleCatCohomologyClassOfIso_apply,
    HomologicalComplex.homologyMap_homologyπ_moduleCatCyclesMk]
  refine (HomologicalComplex.moduleCatCohomologyClassOfIso_eq_homologyπ _ _ _ _ _ _ _ ?_).symm
  rw [HomologicalComplex.iCycles_moduleCatCyclesMk]
  simpa using ConcreteCategory.congr_hom (map_f f q) ((deRhamComplexXIso K A q).inv ω.1)
end deRhamComplex
end ComplexFunctoriality

/-! ### Vanishing above the number of variables -/

/-- When `Omega R A` is subsingleton, all positive-degree de Rham cohomology groups vanish. -/
theorem subsingleton_deRhamCohomology_succ_of_subsingleton {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [Subsingleton (Omega R A)] (q : ℕ) :
    Subsingleton (deRhamCohomology R A (q + 1)) :=
  have := exteriorPower.subsingleton_succ_of_subsingleton (R := A) (M := Omega R A) q
  subsingleton_deRhamCohomology_of_closedForms_le_exactForms R A (q := q + 1)
    fun ω _ ↦ Subsingleton.elim ω 0 ▸ zero_mem _

section Washnitzer
variable {σ K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- On `washnitzerAlgebra σ K`, every exterior power of `Omega` above `Nat.card σ` vanishes. -/
theorem subsingleton_forms_washnitzer_of_card_lt [Finite σ] {q : ℕ} (hq : Nat.card σ < q) :
    Subsingleton (⋀[washnitzerAlgebra σ K]^q (Omega K (washnitzerAlgebra σ K))) :=
  exteriorPower.subsingleton_of_span_eq_top_of_card_lt (washnitzerBasis σ K)
    (washnitzerBasis σ K).span_eq q hq

/-- Overconvergent de Rham cohomology of `washnitzerAlgebra σ K` vanishes for `q > Nat.card σ`. -/
theorem subsingleton_deRhamCohomology_washnitzer_of_card_lt [Finite σ] {q : ℕ}
    (hq : Nat.card σ < q) : Subsingleton (deRhamCohomology K (washnitzerAlgebra σ K) q) :=
  have := subsingleton_forms_washnitzer_of_card_lt (K := K) hq
  subsingleton_deRhamCohomology_of_closedForms_le_exactForms K (washnitzerAlgebra σ K)
    fun ω _ ↦ Subsingleton.elim ω 0 ▸ zero_mem _
end Washnitzer

end TauCeti.Dagger.Omega
