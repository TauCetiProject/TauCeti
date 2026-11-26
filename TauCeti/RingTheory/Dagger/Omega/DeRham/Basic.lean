/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.RingTheory.Dagger.Omega.DeRham.Derivative

/-!
# The overconvergent de Rham complex and its functoriality

For any Noetherian commutative `R`-algebra `A` with finite `Omega R A` (in particular any `K`-dagger
algebra over a complete ultrametric normed field `K`), constructs Grosse-Klönne's overconvergent
de Rham complex `Omega.deRhamComplex R A` and cohomology `Omega.deRhamCohomology R A q` from
`Omega.extDerivPow`, functorial in `K`-dagger algebras over a complete ultrametric normed
field `K`.

## References

* E. Grosse-Klönne, *Finiteness of de Rham cohomology in rigid analysis*, Duke Math. J. 113
  (2002), §1.2.
* K. Kedlaya, *Finiteness of rigid cohomology with coefficients*, Duke Math. J. 134 (2006), §3.1.
-/

public section
noncomputable section

open CategoryTheory

namespace TauCeti.Dagger.Omega

/-! ### Overconvergent de Rham complex and cohomology -/

section DeRham
variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] [IsNoetherianRing A]
  [Module.Finite A (Omega R A)]

/-- **The universally finite (overconvergent) de Rham cochain complex**
`0 → ⋀⁰ Ω¹ → ⋀¹ Ω¹ → ⋀² Ω¹ → ⋯` in `ModuleCat R`. -/
def deRhamComplex : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun q ↦ ModuleCat.of R (⋀[A]^q (Omega R A)))
    (fun q ↦ ModuleCat.ofHom (extDerivPow R A q))
    (fun q ↦ ModuleCat.hom_ext (extDerivPow_comp_extDerivPow q))

/-- Canonical identification of `(deRhamComplex R A).X q` with `⋀[A]^q (Omega R A)`. -/
def deRhamComplexXIso (q : ℕ) : (deRhamComplex R A).X q ≅ ModuleCat.of R (⋀[A]^q (Omega R A)) :=
  Iso.refl _

@[reassoc] theorem deRhamComplex_d (q : ℕ) :
    (deRhamComplex R A).d q (q + 1) ≫ (deRhamComplexXIso R A (q + 1)).hom =
      (deRhamComplexXIso R A q).hom ≫ ModuleCat.ofHom (extDerivPow R A q) := by
  simp [deRhamComplexXIso, deRhamComplex, CochainComplex.of_d]
theorem deRhamComplex_d_apply (q : ℕ) (x : (deRhamComplex R A).X q) :
    (deRhamComplex R A).d q (q + 1) x =
      (deRhamComplexXIso R A (q + 1)).inv
        (extDerivPow R A q ((deRhamComplexXIso R A q).hom x)) := by
  rw [(Iso.eq_comp_inv _).mpr (deRhamComplex_d R A q), ModuleCat.comp_apply, ModuleCat.comp_apply,
    ConcreteCategory.hom_ofHom]

/-- The `R`-submodule of closed `q`-forms `ker (d : Ω^q → Ω^{q+1})`. -/
def closedForms (q : ℕ) : Submodule R (⋀[A]^q (Omega R A)) :=
  LinearMap.ker (extDerivPow R A q)

/-- The `R`-submodule of exact `q`-forms: `⊥` in degree `0` and `range d` in degree `q + 1`. -/
def exactForms : (q : ℕ) → Submodule R (⋀[A]^q (Omega R A))
  | 0 => ⊥
  | q + 1 => LinearMap.range (extDerivPow R A q)

@[simp] theorem mem_closedForms {q : ℕ} (ω : ⋀[A]^q (Omega R A)) :
    ω ∈ closedForms R A q ↔ extDerivPow R A q ω = 0 := Iff.rfl
@[simp] theorem exactForms_zero : exactForms R A 0 = ⊥ := (rfl)
@[simp] theorem exactForms_succ (q : ℕ) :
    exactForms R A (q + 1) = LinearMap.range (extDerivPow R A q) := (rfl)
theorem exactForms_le_closedForms : (q : ℕ) → exactForms R A q ≤ closedForms R A q
  | 0 => by simp
  | q + 1 => LinearMap.range_le_ker_iff.mpr (extDerivPow_comp_extDerivPow q)
theorem extDerivPow_mem_closedForms (q : ℕ) (ω : ⋀[A]^q (Omega R A)) :
    extDerivPow R A q ω ∈ closedForms R A (q + 1) :=
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
        (fun ω ↦ deRhamComplex_d_eq_zero_of_mem_closedForms R A q ω.property) :=
  LinearMap.ext fun _ ↦ by
    rw [mk, HomologicalComplex.moduleCatCohomologyClassOfIso_apply,
      HomologicalComplex.moduleCatHomologyClass_apply]
    congr 1

/-- Every cohomology class in `deRhamCohomology R A q` has a closed `q`-form representative. -/
theorem mk_surjective (q : ℕ) : Function.Surjective (mk R A q) :=
  (deRhamComplex R A).moduleCatCohomologyClassOfIso_surjective _ _ _ _ q
/-- A closed `q`-form represents zero in `deRhamCohomology R A q` iff it is exact. -/
@[simp] theorem mk_eq_zero_iff (q : ℕ) (ω : closedForms R A q) :
    mk R A q ω = 0 ↔ ω.val ∈ exactForms R A q :=
  (deRhamComplex R A).moduleCatCohomologyClassOfIso_eq_zero_iff _ _ (exactForms R A) _ _
    (HomologicalComplex.moduleCat_mem_iff_exists_d_eq_inv _ _ _ (deRhamComplex_d R A)
      (exactForms_zero R A) (exactForms_succ R A)) q ω
/-- Two closed `q`-forms represent the same cohomology class iff their difference is exact. -/
theorem mk_eq_iff (q : ℕ) (ω η : closedForms R A q) :
    mk R A q ω = mk R A q η ↔ (ω - η).val ∈ exactForms R A q := by
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
    hc ▸ (deRhamCohomology.mk_eq_zero_iff R A q ω).mpr (h ω.property)

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
  [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]

namespace closedForms
/-- Pullback of closed overconvergent `q`-forms along `f : A →ₐ[K] B`. -/
def map (f : A →ₐ[K] B) (q : ℕ) : closedForms K A q →ₗ[K] closedForms K B q :=
  ((formsMap f q).domRestrict (closedForms K A q)).codRestrict (closedForms K B q) fun ω ↦ by
    rw [mem_closedForms, LinearMap.domRestrict_apply, extDerivPow_formsMap,
      (mem_closedForms K A ω.val).mp ω.property, map_zero]
@[simp] theorem coe_map (f : A →ₐ[K] B) (q : ℕ) (ω : closedForms K A q) :
    (map f q ω).val = formsMap f q ω.val := (rfl)
@[simp] theorem map_id (q : ℕ) : map (AlgHom.id K A) q = LinearMap.id :=
  LinearMap.ext fun _ ↦ Subtype.ext (by simp)
theorem map_comp (g : B →ₐ[K] C) (f : A →ₐ[K] B) (q : ℕ) :
    map (g.comp f) q = (map g q) ∘ₗ (map f q) :=
  LinearMap.ext fun _ ↦ Subtype.ext (by simp [formsMap_comp])
theorem map_mem_exactForms (f : A →ₐ[K] B) : ∀ (q : ℕ) (ω : closedForms K A q),
    ω.val ∈ exactForms K A q → (map f q ω).val ∈ exactForms K B q
  | 0, ω, hω => by rw [exactForms_zero, Submodule.mem_bot] at hω ⊢; rw [coe_map, hω, map_zero]
  | q + 1, _, ⟨η, hη⟩ => ⟨formsMap f q η, by rw [coe_map, extDerivPow_formsMap, hη]⟩
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
  rw [map, LinearMap.equivOfSurjective_apply, LinearMap.comp_apply]
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
  [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]

namespace deRhamComplex
/-- The cochain map `deRhamComplex K A ⟶ deRhamComplex K B` induced by `f : A →ₐ[K] B`. -/
def map (f : A →ₐ[K] B) : deRhamComplex K A ⟶ deRhamComplex K B :=
  CochainComplex.ofHom
    (fun q ↦ (deRhamComplexXIso K A q).hom ≫ ModuleCat.ofHom (formsMap f q) ≫
      (deRhamComplexXIso K B q).inv) fun q ↦ by
      have hcomm : ModuleCat.ofHom (formsMap f q) ≫ ModuleCat.ofHom (extDerivPow K B q) =
          ModuleCat.ofHom (extDerivPow K A q) ≫ ModuleCat.ofHom (formsMap f (q + 1)) :=
        ModuleCat.hom_ext (extDerivPow_comp_formsMap f q)
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
  simpa using ConcreteCategory.congr_hom (map_f f q) ((deRhamComplexXIso K A q).inv ω.val)
end deRhamComplex
end ComplexFunctoriality

/-! ### Vanishing above the number of variables -/

/-- When `Omega R A` is subsingleton and `A` is Noetherian, all positive-degree de Rham
cohomology groups vanish. -/
theorem subsingleton_deRhamCohomology_succ_of_subsingleton {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [IsNoetherianRing A] [Subsingleton (Omega R A)] (q : ℕ) :
    Subsingleton (deRhamCohomology R A (q + 1)) :=
  have := exteriorPower.subsingleton_succ_of_subsingleton (R := A) (M := Omega R A) q
  subsingleton_deRhamCohomology_of_closedForms_le_exactForms R A (q := q + 1)
    fun ω _ ↦ Subsingleton.elim ω 0 ▸ zero_mem _

section Washnitzer
variable {σ K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Over a complete ultrametric normed field `K`, overconvergent de Rham cohomology of
`washnitzerAlgebra σ K` vanishes for `q > Nat.card σ`. -/
theorem subsingleton_deRhamCohomology_washnitzer_of_card_lt [Finite σ] {q : ℕ}
    (hq : Nat.card σ < q) : Subsingleton (deRhamCohomology K (washnitzerAlgebra σ K) q) :=
  have := subsingleton_forms_washnitzer_of_card_lt (K := K) hq
  subsingleton_deRhamCohomology_of_closedForms_le_exactForms K (washnitzerAlgebra σ K)
    fun ω _ ↦ Subsingleton.elim ω 0 ▸ zero_mem _
end Washnitzer

end TauCeti.Dagger.Omega
