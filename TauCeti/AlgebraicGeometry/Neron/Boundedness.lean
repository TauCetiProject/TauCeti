/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Scheme
public import TauCeti.AlgebraicGeometry.GroupScheme.MultiplicativeGroup
public import TauCeti.AlgebraicGeometry.Neron.Model
import TauCeti.AlgebraicGeometry.Scheme.SectionsBaseChange

/-!
# Bounded denominators and the nonexistence of finite-type Néron models of split tori

Let `K` be a localization of a ring `R` and let `M` be a marked model over `R` whose test
class contains the identity of `Spec R`. Every global regular function on its marked fibre has
a common denominator for its values at all `K`-points. Flat base change for global sections
(`TauCeti.AlgebraicGeometry.isBaseChange_sectionsBaseChange`) on the quasi-compact
quasi-separated total space supplies an integral numerator. Each
`K`-point extends to an `R`-section on which to evaluate that numerator.

Over the fraction field of a domain with a nonzero nonunit `r`, a split torus of positive rank
violates this bound. For any proposed denominator `d ≠ 0`, a coordinate takes the value
`1 / (d * r)`, and multiplying by `d` leaves `1 / r` outside the base ring. Thus the torus has
no finite-type Néron model, even for étale tests alone.

## References

* S. Bosch, W. Lütkebohmert and M. Raynaud, *Néron Models*, §§1.1–1.2 and 10.1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj nonZeroDivisors

namespace TauCeti.AlgebraicGeometry.Neron

universe u

open GroupScheme

variable {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
  {P : ∀ ⦃X Y : Scheme.{u}⦄, (X ⟶ Y) → Prop} {A : Over (Spec (.of K))}

/-- After multiplication by a denominator from the base, a regular function on the marked fibre
is the restriction of a global regular function on the model. -/
theorem Model.exists_appTop_genericι_eq_mul (M : Model P (Spec.algebraMap R K) A)
    (D : Submonoid R) [IsLocalization D K] (b : Γ(A.left, ⊤)) :
    ∃ (a : Γ(M.model.left, ⊤)) (d : D), M.genericι.appTop a =
      A.hom.appTop ((Scheme.ΓSpecIso (.of K)).inv (algebraMap R K d)) * b := by
  let _ : M.model.left.Over (Spec (.of R)) := ⟨M.model.hom⟩
  let _ : A.left.Over (Spec (.of K)) := ⟨A.hom⟩
  have := QuasiCompact.compactSpace_of_compactSpace M.model.hom
  have := quasiSeparatedSpace_of_quasiSeparated M.model.hom
  -- On the quasi-compact quasi-separated model, localizing the base localizes global sections.
  let X := M.model.left
  let Y := A.left
  let : Algebra R Γ(X, ⊤) := ((X.baseRingToStructurePresheaf R).app (op ⊤)).hom.toAlgebra
  let : Algebra K Γ(Y, ⊤) := ((Y.baseRingToStructurePresheaf K).app (op ⊤)).hom.toAlgebra
  let : Module R Γ(Y, ⊤) := Module.compHom _ (algebraMap R K)
  have : IsScalarTower R K Γ(Y, ⊤) := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have := IsLocalization.flat K D
  have H : IsPullback M.genericι (Y ↘ Spec (.of K)) (X ↘ Spec (.of R))
      (Spec.algebraMap R K) := M.isPullback_genericι
  have htop : (⊤ : Y.Opens) = M.genericι ⁻¹ᵁ (⊤ : X.Opens) := by simp
  have := (isLocalizedModule_iff_isBaseChange D K _).2
    (isBaseChange_sectionsBaseChange H isCompact_univ isQuasiSeparated_univ htop)
  obtain ⟨⟨a, d⟩, hd⟩ := IsLocalizedModule.surj D (sectionsBaseChange H htop.le) b
  have happ : M.genericι.appLE ⊤ ⊤ htop.le = M.genericι.appTop := M.genericι.appLE_eq_app
  refine ⟨a, d, ?_⟩
  calc
    _ = (Y.baseRingToStructurePresheaf K).app (op ⊤) (algebraMap R K d) * b := by
      rw [← happ, ← sectionsBaseChange_apply H htop.le]
      -- The restricted scalar action of `d` is multiplication by its image on `Y`.
      exact hd.symm
    _ = _ := by
      -- The local `Over` instance uses `A.hom` as the structure morphism of `Y`.
      have hbase : (Y ↘ Spec (.of K)).appLE ⊤ ⊤ le_top = A.hom.appTop :=
        A.hom.appLE_eq_app
      rw [Scheme.baseRingToStructurePresheaf_app_eq_appLE, CommRingCat.comp_apply, hbase]

/-- For a regular function on the marked fibre, one denominator makes its value at every
section over the localized base lie in the image of the base ring. -/
theorem Model.exists_isInteger_mul_eval (M : Model P (Spec.algebraMap R K) A)
    (D : Submonoid R) [IsLocalization D K] (hP : P (𝟙 (Spec (.of R))))
    (b : Γ(A.left, ⊤)) : ∃ d : D, ∀ x : Over.mk (𝟙 (Spec (.of K))) ⟶ A,
      IsLocalization.IsInteger R
        (algebraMap R K d * (Scheme.ΓSpecIso (.of K)).hom (x.left.appTop b)) := by
  obtain ⟨a, d, ha⟩ := M.exists_appTop_genericι_eq_mul D b
  refine ⟨d, fun x ↦ ?_⟩
  obtain ⟨s, hs⟩ := (M.existsUnique_section hP x).exists
  refine ⟨(Scheme.ΓSpecIso (.of R)).hom (s.left.appTop a), ?_⟩
  have hnat := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality
    (CommRingCat.ofHom (algebraMap R K))) (s.left.appTop a)
  have heval := ConcreteCategory.congr_hom (congrArg Scheme.Hom.appTop hs) a
  have hconst := ConcreteCategory.congr_hom (congrArg Scheme.Hom.appTop (Over.w x))
    ((Scheme.ΓSpecIso (.of K)).inv (algebraMap R K d))
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at heval hconst
  calc
    _ = (Scheme.ΓSpecIso (.of K)).hom ((Spec.algebraMap R K).appTop (s.left.appTop a)) :=
      hnat.symm
    _ = _ := by
      rw [heval, ha]
      simp [hconst]

/-- If one regular function takes every unit value on sections of the marked fibre, then
the localization map is surjective. -/
theorem Model.surjective_algebraMap_of_units_subset_range
    (M : Model P (Spec.algebraMap R K) A) (D : Submonoid R) [IsLocalization D K]
    (hP : P (𝟙 (Spec (.of R)))) (b : Γ(A.left, ⊤))
    (hb : ∀ u : Γ(Spec (.of K), ⊤)ˣ, ∃ x : Over.mk (𝟙 (Spec (.of K))) ⟶ A,
      x.left.appTop b = (u : Γ(Spec (.of K), ⊤))) : Function.Surjective (algebraMap R K) := by
  obtain ⟨d, hd⟩ := M.exists_isInteger_mul_eval D hP b
  have hint (u : Kˣ) : IsLocalization.IsInteger R (u : K) := by
    let v := (IsLocalization.map_units K d).unit⁻¹ * u
    let e := (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv
    obtain ⟨x, hx⟩ := hb (Units.map e.symm.toMonoidHom v)
    have he : (Scheme.ΓSpecIso (.of K)).hom (x.left.appTop b) = v := by
      rw [hx]
      exact e.apply_symm_apply _
    simpa [he, v, ← mul_assoc] using hd x
  intro y
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq D y
  rw [IsLocalization.mk'_eq_mul_mk'_one]
  exact IsLocalization.isInteger_mul ⟨a, rfl⟩
    (hint (unitOfInvertible (IsLocalization.mk' K 1 s)))

section FractionField

variable [IsDomain R] [IsFractionRing R K]

/-- The multiplicative group over the fraction field of a domain that is not a field admits no
finite-type marked model for a test class containing the base. -/
theorem isEmpty_model_Gm (hR : ¬ IsField R) (hP : P (𝟙 (Spec (.of R)))) :
    IsEmpty (Model P (Spec.algebraMap R K) (Gm (Spec (.of K))).X) := by
  refine ⟨fun M ↦ hR ((IsFractionRing.surjective_iff_isField (K := K)).mp ?_)⟩
  let G := (Gm (Spec (.of K))).X
  apply M.surjective_algebraMap_of_units_subset_range R⁰ hP
    (Gm.pointsMulEquiv G (𝟙 G) : Γ(G.left, ⊤))
  intro u
  let T := Over.mk (𝟙 (Spec (.of K)))
  let x := (Gm.pointsMulEquiv T).symm u
  refine ⟨x, ?_⟩
  calc
    _ = (Gm.pointsMulEquiv T (x ≫ 𝟙 G) : Γ(T.left, ⊤)) :=
      (congrArg Units.val (Gm.pointsMulEquiv_naturality x (𝟙 G))).symm
    _ = _ := by rw [Category.comp_id, MulEquiv.apply_symm_apply]

/-- A positive-rank split torus over the fraction field of a domain that is not a field admits
no finite-type marked model for a test class containing the base. -/
theorem isEmpty_model_splitTorus (hR : ¬ IsField R) (hP : P (𝟙 (Spec (.of R))))
    (σ : Type u) [Finite σ] [Nonempty σ] :
    IsEmpty (Model P (Spec.algebraMap R K) (SplitTorus.groupScheme K σ).X) := by
  classical
  obtain ⟨i⟩ := ‹Nonempty σ›
  refine ⟨fun M ↦ hR ((IsFractionRing.surjective_iff_isField (K := K)).mp ?_)⟩
  let C := SplitTorus.characterGroup σ
  let G := (SplitTorus.groupScheme K σ).X
  let c : C := Multiplicative.ofAdd (Finsupp.single i 1)
  let t := DiagonalizableGroup.schemePointsAlgΓMulEquiv C G (𝟙 G) c
  apply M.surjective_algebraMap_of_units_subset_range R⁰ hP (t : Γ(G.left, ⊤))
  intro u
  let T := Over.mk (𝟙 (Spec (.of K)))
  let χ : C →* Γ(T.left, ⊤)ˣ := freeAbelianCharEquiv.symm (fun _ ↦ u)
  let x := (DiagonalizableGroup.schemePointsAlgΓMulEquiv C T).symm χ
  refine ⟨x, ?_⟩
  have hx := congrArg (fun f : C →* Γ(T.left, ⊤)ˣ ↦ (f c : Γ(T.left, ⊤)))
    (DiagonalizableGroup.schemePointsAlgΓMulEquiv_precomp C x (𝟙 G))
  calc
    _ = ((DiagonalizableGroup.schemePointsAlgΓMulEquiv C T (x ≫ 𝟙 G)) c : Γ(T.left, ⊤)) :=
      hx.symm
    _ = _ := by
      rw [Category.comp_id, MulEquiv.apply_symm_apply]
      exact congrArg Units.val (freeAbelianCharEquiv_symm_apply_ofAdd_single (fun _ ↦ u) i)

end FractionField

end TauCeti.AlgebraicGeometry.Neron
