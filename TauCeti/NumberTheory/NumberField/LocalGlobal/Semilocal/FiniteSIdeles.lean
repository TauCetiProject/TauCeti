/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Adeles.GaloisAction
public import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.FiniteAdele
public import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.IntegralUnits
public import TauCeti.RepresentationTheory.Pi
public import TauCeti.RingTheory.DedekindDomain.PrimesAbove

/-!
# The finite `S`-ideles as a product of semi-local factors

Let `L/K` be an extension of number fields and `S` a finite set of finite places of `K`. The
**finite `S`-ideles** of `L` are the finite ideles whose component at every finite place `w` of
`L` not above `S` is a unit of `𝒪_w`:

```text
I_{L,S}^f = ∏_{v ∈ S} ∏_{w ∣ v} L_wˣ × ∏_{v ∉ S} ∏_{w ∣ v} 𝒪_wˣ.
```

The components of a finite idele at the places above a finite place `v` of `K` form a unit of
the semi-local algebra `K_v ⊗[K] L ≃ ∏_{w ∣ v} L_w` (`finiteIdeleSemilocalHom`), and a finite
idele is determined by these semi-local components
(`eq_of_forall_finiteIdeleSemilocalHom_eq`). Conversely, a family of semi-local units which are
integral at all but finitely many places is the family of semi-local components of a finite idele
(`finiteIdeleOfSemilocalUnits`). Taking components is equivariant for the Galois action of
`Aut(L/K)` on finite adeles (`GlobalNumberFields.finiteAdeleGaloisAction`) and on the semi-local
algebras (`semilocalGaloisHom`).

Together, these identify the finite `S`-ideles, as an integral representation of `Aut(L/K)`, with
the product over the places of `K` of the semi-local unit groups `(K_v ⊗[K] L)ˣ` for `v ∈ S` and
of the integral semi-local unit groups for `v ∉ S` (`finiteSIdelesPiIso`). This is the form in
which the Tate cohomology of the `S`-ideles is computed one place at a time, through Shapiro's
lemma for each semi-local factor.

## Main definitions

* `TauCeti.finiteIdeleSemilocalHom L v`: the components above `v` of a finite idele of `L`, as a
  unit of `K_v ⊗[K] L`.
* `TauCeti.finiteIdeleOfSemilocalUnits`: the finite idele with prescribed semi-local components.
* `TauCeti.finiteSIdeles L S`: the finite `S`-ideles of `L`, as a subgroup of the finite ideles.
* `TauCeti.finiteSIdelesRep L S`: the finite `S`-ideles, as an integral representation of
  `Aut(L/K)`.
* `TauCeti.finiteSIdelesPiRep L S`: the product of the semi-local factors of the finite
  `S`-ideles.
* `TauCeti.finiteSIdelesPiIso L S`: the isomorphism of representations between the two.

## Main results

* `TauCeti.eq_of_forall_finiteIdeleSemilocalHom_eq`: a finite idele is determined by its
  semi-local components.
* `TauCeti.finiteIdeleSemilocalHom_map_finiteAdeleGaloisAction`: taking semi-local components is
  Galois equivariant.
* `TauCeti.mem_finiteSIdeles_iff_valued`: a finite idele is an `S`-idele exactly when its
  components at the places not above `S` have valuation one.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, §2.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §2.
-/

public section
noncomputable section

open CategoryTheory IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct AdicCompletionExtension

namespace TauCeti

local notation "𝒪" => _root_.NumberField.RingOfIntegers

universe u

variable {K : Type u} [Field K] [NumberField K] (L : Type u) [Field L] [NumberField L]
  [Algebra K L]

/-! ### The semi-local components of a finite idele -/

section SemilocalComponent

variable (v : HeightOneSpectrum (𝒪 K))

/-- **The semi-local component of a finite idele.** The components of a finite idele of `L` at
the places of `L` above the finite place `v` of `K`, as a unit of `K_v ⊗[K] L`. -/
def finiteIdeleSemilocalHom : (FiniteAdeleRing (𝒪 L) L)ˣ →* (v.adicCompletion K ⊗[K] L)ˣ :=
  Units.map (finiteAdeleSemilocalHom L v)

variable {L v}

/-- The semi-local component of a finite idele, as a unit of `K_v ⊗[K] L`, has the semi-local
component of the underlying finite adele as its value. -/
@[simp]
theorem coe_finiteIdeleSemilocalHom (a : (FiniteAdeleRing (𝒪 L) L)ˣ) :
    (finiteIdeleSemilocalHom L v a : v.adicCompletion K ⊗[K] L) =
      finiteAdeleSemilocalHom L v a :=
  (rfl)

/-- Under the semi-local decomposition, the semi-local component of a finite idele is its family
of components at the places above `v`. -/
private theorem semilocalEquiv_finiteIdeleSemilocalHom (a : (FiniteAdeleRing (𝒪 L) L)ˣ)
    (w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) :
    semilocalEquiv L v (finiteIdeleSemilocalHom L v a) w = (a : FiniteAdeleRing (𝒪 L) L) w.1 := by
  rw [coe_finiteIdeleSemilocalHom, semilocalEquiv_finiteAdeleSemilocalHom]

omit [NumberField K] [NumberField L] in
/-- A place of `L` lying over the place `v` of `K` contracts to `v`. -/
private theorem under_eq_of_liesOver {w : HeightOneSpectrum (𝒪 L)}
    (hw : w.asIdeal.LiesOver v.asIdeal) :
    w.under (𝒪 K) = v :=
  asIdeal_injective hw.over.symm

/-- **A finite idele is determined by its semi-local components.** -/
theorem eq_of_forall_finiteIdeleSemilocalHom_eq {a b : (FiniteAdeleRing (𝒪 L) L)ˣ}
    (h : ∀ v : HeightOneSpectrum (𝒪 K),
      finiteIdeleSemilocalHom L v a = finiteIdeleSemilocalHom L v b) :
    a = b := by
  refine Units.ext (FiniteAdeleRing.ext L fun w ↦ ?_)
  rw [← semilocalEquiv_finiteIdeleSemilocalHom (v := w.under (𝒪 K)) a ⟨w, inferInstance⟩,
    ← semilocalEquiv_finiteIdeleSemilocalHom (v := w.under (𝒪 K)) b ⟨w, inferInstance⟩,
    h (w.under (𝒪 K))]

variable (v) in
/-- **Taking semi-local components is Galois equivariant.** The semi-local component of the
transport of a finite idele along `σ ∈ Aut(L/K)` is the image of its semi-local component under
`id ⊗ σ`. -/
theorem finiteIdeleSemilocalHom_map_finiteAdeleGaloisAction (σ : L ≃ₐ[K] L)
    (a : (FiniteAdeleRing (𝒪 L) L)ˣ) :
    finiteIdeleSemilocalHom L v
        (Units.map (GlobalNumberFields.finiteAdeleGaloisAction K L σ : _ →* _) a) =
      Units.map (semilocalGaloisHom L v σ : _ →* _) (finiteIdeleSemilocalHom L v a) := by
  have h : (semilocalGaloisHom L v σ).toAlgHom =
      Algebra.TensorProduct.map (AlgHom.id _ _) (σ : L →ₐ[K] L) :=
    Algebra.TensorProduct.ext' fun _ _ ↦ by simp
  ext : 1
  rw [coe_finiteIdeleSemilocalHom, Units.coe_map, Units.coe_map, coe_finiteIdeleSemilocalHom,
    MonoidHom.coe_ofClass, GlobalNumberFields.finiteAdeleGaloisAction_apply,
    finiteAdeleSemilocalHom_finiteAdeleEquiv]
  exact (DFunLike.congr_fun h _).symm

/-- **The finite idele with prescribed semi-local components.** A family of units
`y v ∈ (K_v ⊗[K] L)ˣ`, integral in every component for all but finitely many `v`, assembles to a
finite idele of `L` whose component at a place `w` above `v` is the component of `y v` at `w`. -/
def finiteIdeleOfSemilocalUnits (y : ∀ v : HeightOneSpectrum (𝒪 K), (v.adicCompletion K ⊗[K] L)ˣ)
    (hy : ∀ᶠ v in Filter.cofinite, y v ∈ semilocalIntegralUnits L v) :
    (FiniteAdeleRing (𝒪 L) L)ˣ :=
  RestrictedProduct.mkUnit
    (fun w ↦ Units.map ((Pi.evalMonoidHom (fun w' :
        {w' : HeightOneSpectrum (𝒪 L) // w'.asIdeal.LiesOver (w.under (𝒪 K)).asIdeal} ↦
          w'.1.adicCompletion L) ⟨w, inferInstance⟩).comp
        (semilocalEquiv L (w.under (𝒪 K)) : _ →* _)) (y (w.under (𝒪 K))))
    (by
      filter_upwards [(tendsto_under_cofinite (𝒪 K) (𝒪 L)).eventually hy] with w hw
      exact adicCompletionIntegers.mem_units_iff_valued_eq_one.2
        ((mem_semilocalIntegralUnits_iff _ _).1 hw ⟨w, inferInstance⟩))

/-- The semi-local components of `finiteIdeleOfSemilocalUnits y hy` are the prescribed units
`y v`. -/
@[simp]
theorem finiteIdeleSemilocalHom_finiteIdeleOfSemilocalUnits
    (y : ∀ v : HeightOneSpectrum (𝒪 K), (v.adicCompletion K ⊗[K] L)ˣ)
    (hy : ∀ᶠ v in Filter.cofinite, y v ∈ semilocalIntegralUnits L v) :
    finiteIdeleSemilocalHom L v (finiteIdeleOfSemilocalUnits y hy) = y v := by
  refine Units.ext ((semilocalEquiv L v).injective (funext fun w ↦ ?_))
  rw [semilocalEquiv_finiteIdeleSemilocalHom]
  obtain ⟨w, hw⟩ := w
  obtain rfl := under_eq_of_liesOver hw
  rfl

end SemilocalComponent

/-! ### The finite `S`-ideles -/

section SIdeles

variable (S : Finset (HeightOneSpectrum (𝒪 K)))

/-- **The finite `S`-ideles.** For a finite set `S` of finite places of `K`, the finite ideles of
`L` whose semi-local component at every finite place `v ∉ S` of `K` is integral, that is, whose
component at every place of `L` not above `S` is a unit of `𝒪_w`. -/
def finiteSIdeles : Subgroup (FiniteAdeleRing (𝒪 L) L)ˣ :=
  ⨅ (v : HeightOneSpectrum (𝒪 K)) (_ : v ∉ S),
    (semilocalIntegralUnits L v).comap (finiteIdeleSemilocalHom L v)

variable {L S}

/-- A finite idele is an `S`-idele exactly when its semi-local components outside `S` are
integral. -/
@[simp]
theorem mem_finiteSIdeles_iff {a : (FiniteAdeleRing (𝒪 L) L)ˣ} :
    a ∈ finiteSIdeles L S ↔
      ∀ v ∉ S, finiteIdeleSemilocalHom L v a ∈ semilocalIntegralUnits L v := by
  simp [finiteSIdeles]

/-- A finite idele is an `S`-idele exactly when its component at every place of `L` not above
`S` has valuation one. -/
theorem mem_finiteSIdeles_iff_valued {a : (FiniteAdeleRing (𝒪 L) L)ˣ} :
    a ∈ finiteSIdeles L S ↔
      ∀ w : HeightOneSpectrum (𝒪 L), w.under (𝒪 K) ∉ S →
        Valued.v ((a : FiniteAdeleRing (𝒪 L) L) w) = 1 := by
  simp only [mem_finiteSIdeles_iff, mem_semilocalIntegralUnits_iff,
    semilocalEquiv_finiteIdeleSemilocalHom]
  refine ⟨fun h w hw ↦ h _ hw ⟨w, inferInstance⟩, fun h v hv w ↦ h w.1 ?_⟩
  rwa [under_eq_of_liesOver w.2]

/-- The Galois action on finite ideles preserves the finite `S`-ideles. -/
theorem map_finiteAdeleGaloisAction_mem_finiteSIdeles (σ : L ≃ₐ[K] L)
    {a : (FiniteAdeleRing (𝒪 L) L)ˣ} (ha : a ∈ finiteSIdeles L S) :
    Units.map (GlobalNumberFields.finiteAdeleGaloisAction K L σ : _ →* _) a ∈
      finiteSIdeles L S := by
  rw [mem_finiteSIdeles_iff] at ha ⊢
  intro v hv
  rw [finiteIdeleSemilocalHom_map_finiteAdeleGaloisAction]
  exact semilocalGaloisHom_mem_semilocalIntegralUnits v σ (ha v hv)

variable (L S) in
/-- The Galois action of `Aut(L/K)` on the finite `S`-ideles, through the Galois action on finite
adeles. -/
instance finiteSIdelesMulDistribMulAction :
    MulDistribMulAction (L ≃ₐ[K] L) (finiteSIdeles L S) := by
  letI : MulSemiringAction (L ≃ₐ[K] L) (FiniteAdeleRing (𝒪 L) L) :=
    MulSemiringAction.compHom _ (GlobalNumberFields.finiteAdeleGaloisAction K L)
  letI : MulDistribMulAction (L ≃ₐ[K] L) (FiniteAdeleRing (𝒪 L) L)ˣ :=
    Units.mulDistribMulActionRight
  letI : SMul (L ≃ₐ[K] L) (finiteSIdeles L S) :=
    ⟨fun σ a ↦ ⟨Units.map (GlobalNumberFields.finiteAdeleGaloisAction K L σ : _ →* _) a.1,
      map_finiteAdeleGaloisAction_mem_finiteSIdeles σ a.2⟩⟩
  exact Subtype.coe_injective.mulDistribMulAction (finiteSIdeles L S).subtype fun _ _ ↦ rfl

/-- The Galois action on a finite `S`-idele is the Galois action on the underlying finite idele. -/
@[simp]
theorem coe_smul_finiteSIdeles (σ : L ≃ₐ[K] L) (a : finiteSIdeles L S) :
    ((σ • a : finiteSIdeles L S) : (FiniteAdeleRing (𝒪 L) L)ˣ) =
      Units.map (GlobalNumberFields.finiteAdeleGaloisAction K L σ : _ →* _)
        (a : (FiniteAdeleRing (𝒪 L) L)ˣ) :=
  (rfl)

variable (L S)

/-- The finite `S`-ideles, as an integral representation of `Aut(L/K)`. -/
abbrev finiteSIdelesRep : Rep ℤ (L ≃ₐ[K] L) :=
  Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (finiteSIdeles L S)

/-- The product, over the finite places `v` of `K`, of the semi-local units `(K_v ⊗[K] L)ˣ` for
`v ∈ S` and of the integral semi-local units `∏_{w ∣ v} 𝒪_wˣ` for `v ∉ S`, as an integral
representation of `Aut(L/K)`. -/
abbrev finiteSIdelesPiRep : Rep ℤ (L ≃ₐ[K] L) :=
  Rep.pi (Sum.elim (fun v : S ↦ semilocalUnitsRep L v.1)
    (fun v : {v : HeightOneSpectrum (𝒪 K) // v ∉ S} ↦ semilocalIntegralUnitsRep L v.1))

variable {L S} in
/-- The semi-local component at a place `v` of a finite `S`-idele, as a morphism of
representations. -/
private def finiteSIdelesToSemilocalUnits (v : HeightOneSpectrum (𝒪 K)) :
    finiteSIdelesRep L S ⟶ semilocalUnitsRep L v :=
  Rep.ofHom <| LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    ((finiteIdeleSemilocalHom L v).comp (finiteSIdeles L S).subtype).toAdditive.toIntLinearMap
    fun σ a ↦ congrArg Additive.ofMul
      (finiteIdeleSemilocalHom_map_finiteAdeleGaloisAction v σ a.toMul.1)

variable {L S} in
/-- The semi-local component at a place `v ∉ S` of a finite `S`-idele, which is integral, as a
morphism of representations. -/
private def finiteSIdelesToSemilocalIntegralUnits (v : HeightOneSpectrum (𝒪 K)) (hv : v ∉ S) :
    finiteSIdelesRep L S ⟶ semilocalIntegralUnitsRep L v :=
  Rep.ofHom <| LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (((finiteIdeleSemilocalHom L v).comp (finiteSIdeles L S).subtype).codRestrict
      (semilocalIntegralUnits L v)
      fun a ↦ mem_finiteSIdeles_iff.1 a.2 v hv).toAdditive.toIntLinearMap
    fun σ a ↦ congrArg Additive.ofMul
      (Subtype.ext (finiteIdeleSemilocalHom_map_finiteAdeleGaloisAction v σ a.toMul.1))

/-- The semi-local components of a finite `S`-idele, as a morphism to the product of the
semi-local factors. -/
private def finiteSIdelesPiHom : finiteSIdelesRep L S ⟶ finiteSIdelesPiRep L S :=
  Rep.piLift fun
    | Sum.inl v => finiteSIdelesToSemilocalUnits v.1
    | Sum.inr v => finiteSIdelesToSemilocalIntegralUnits v.1 v.2

private theorem finiteSIdelesPiHom_apply_inl (a : finiteSIdeles L S) (v : S) :
    (finiteSIdelesPiHom L S).hom (Additive.ofMul a) (Sum.inl v) =
      (Additive.ofMul (finiteIdeleSemilocalHom L v.1 a) :
        Additive (v.1.adicCompletion K ⊗[K] L)ˣ) :=
  Rep.piLift_hom_apply _ _ _

private theorem finiteSIdelesPiHom_apply_inr (a : finiteSIdeles L S)
    (v : {v : HeightOneSpectrum (𝒪 K) // v ∉ S}) :
    (finiteSIdelesPiHom L S).hom (Additive.ofMul a) (Sum.inr v) =
      (Additive.ofMul ⟨finiteIdeleSemilocalHom L v.1 a, mem_finiteSIdeles_iff.1 a.2 v.1 v.2⟩ :
        Additive (semilocalIntegralUnits L v.1)) :=
  Rep.piLift_hom_apply _ _ _

private theorem finiteSIdelesPiHom_injective :
    Function.Injective (finiteSIdelesPiHom L S).hom := by
  intro x y h
  obtain ⟨a, rfl⟩ : ∃ a : finiteSIdeles L S, Additive.ofMul a = x := ⟨x.toMul, rfl⟩
  obtain ⟨b, rfl⟩ : ∃ b : finiteSIdeles L S, Additive.ofMul b = y := ⟨y.toMul, rfl⟩
  refine congrArg Additive.ofMul
    (Subtype.ext (eq_of_forall_finiteIdeleSemilocalHom_eq (K := K) fun v ↦ ?_))
  by_cases hv : v ∈ S
  · exact Additive.ofMul.injective ((finiteSIdelesPiHom_apply_inl L S a ⟨v, hv⟩).symm.trans
      ((congrFun h (Sum.inl ⟨v, hv⟩)).trans (finiteSIdelesPiHom_apply_inl L S b ⟨v, hv⟩)))
  · exact congrArg Subtype.val (Additive.ofMul.injective
      ((finiteSIdelesPiHom_apply_inr L S a ⟨v, hv⟩).symm.trans
        ((congrFun h (Sum.inr ⟨v, hv⟩)).trans (finiteSIdelesPiHom_apply_inr L S b ⟨v, hv⟩))))

private theorem finiteSIdelesPiHom_surjective :
    Function.Surjective (finiteSIdelesPiHom L S).hom := by
  classical
  intro z
  -- the prescribed semi-local components, read off the two kinds of factor
  let y (v : HeightOneSpectrum (𝒪 K)) : (v.adicCompletion K ⊗[K] L)ˣ :=
    if hv : v ∈ S then
      Additive.toMul (z (Sum.inl ⟨v, hv⟩) : Additive (v.adicCompletion K ⊗[K] L)ˣ)
    else (Additive.toMul (z (Sum.inr ⟨v, hv⟩) : Additive (semilocalIntegralUnits L v))).1
  have hy (v : HeightOneSpectrum (𝒪 K)) (hv : v ∉ S) : y v ∈ semilocalIntegralUnits L v := by
    simp only [y, hv, dite_false]
    exact (Additive.toMul (z (Sum.inr ⟨v, hv⟩) : Additive (semilocalIntegralUnits L v))).2
  have ha : finiteIdeleOfSemilocalUnits y
      (S.eventually_cofinite_notMem.mono hy) ∈ finiteSIdeles L S :=
    mem_finiteSIdeles_iff.2 fun v hv ↦ by
      rw [finiteIdeleSemilocalHom_finiteIdeleOfSemilocalUnits]
      exact hy v hv
  refine ⟨Additive.ofMul ⟨_, ha⟩, funext fun i ↦ ?_⟩
  rcases i with ⟨v, hv⟩ | ⟨v, hv⟩
  · refine (finiteSIdelesPiHom_apply_inl L S ⟨_, ha⟩ ⟨v, hv⟩).trans ?_
    rw [finiteIdeleSemilocalHom_finiteIdeleOfSemilocalUnits]
    simp only [y, hv, dite_true]
    rfl
  · refine (finiteSIdelesPiHom_apply_inr L S ⟨_, ha⟩ ⟨v, hv⟩).trans ?_
    simp only [finiteIdeleSemilocalHom_finiteIdeleOfSemilocalUnits, y, hv, dite_false]
    rfl

private instance : IsIso (finiteSIdelesPiHom L S) :=
  (ConcreteCategory.isIso_iff_bijective _).2
    ⟨finiteSIdelesPiHom_injective L S, finiteSIdelesPiHom_surjective L S⟩

/-- **The finite `S`-ideles are the product of their semi-local factors.** As integral
representations of `Aut(L/K)`,
`I_{L,S}^f ≅ ∏_{v ∈ S} (K_v ⊗[K] L)ˣ × ∏_{v ∉ S} ∏_{w ∣ v} 𝒪_wˣ`, by taking semi-local
components. -/
def finiteSIdelesPiIso : finiteSIdelesRep L S ≅ finiteSIdelesPiRep L S :=
  asIso (finiteSIdelesPiHom L S)

/-- The factor of `finiteSIdelesPiIso` at a place `v ∈ S` is the semi-local component. -/
@[simp]
theorem finiteSIdelesPiIso_hom_apply_inl (a : finiteSIdeles L S) (v : S) :
    (finiteSIdelesPiIso L S).hom.hom (Additive.ofMul a) (Sum.inl v) =
      (Additive.ofMul (finiteIdeleSemilocalHom L v.1 a) :
        Additive (v.1.adicCompletion K ⊗[K] L)ˣ) :=
  finiteSIdelesPiHom_apply_inl L S a v

/-- The factor of `finiteSIdelesPiIso` at a place `v ∉ S` is the semi-local component, which is
integral. -/
@[simp]
theorem finiteSIdelesPiIso_hom_apply_inr (a : finiteSIdeles L S)
    (v : {v : HeightOneSpectrum (𝒪 K) // v ∉ S}) :
    (finiteSIdelesPiIso L S).hom.hom (Additive.ofMul a) (Sum.inr v) =
      (Additive.ofMul ⟨finiteIdeleSemilocalHom L v.1 a, mem_finiteSIdeles_iff.1 a.2 v.1 v.2⟩ :
        Additive (semilocalIntegralUnits L v.1)) :=
  finiteSIdelesPiHom_apply_inr L S a v

end SIdeles

end TauCeti
