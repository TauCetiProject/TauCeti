/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.SeparableClosure
public import TauCeti.AlgebraicGeometry.IrreducibleComponents.Basic
public import TauCeti.AlgebraicGeometry.Geometrically.Irreducible
public import TauCeti.RingTheory.Spectrum.Prime.ComponentDescent
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import TauCeti.Algebra.TensorProduct.CommonOverfield
import TauCeti.Topology.Irreducible

/-!
# Geometric irreducible components over a finite separable extension

Let `X` be a quasi-compact scheme locally of finite type over a field `K`. Its irreducible
components need not be geometrically irreducible, but they become so after one finite separable
extension: there is a finite separable `L / K` such that, for every field extension `M / L`,
taking preimages under `X_M ⟶ X_L` is a bijection between the irreducible components of `X_L`
and those of `X_M`. This splits and labels the geometric irreducible components of `X`.

The argument runs in two steps.

* For an algebraic extension `Ω / K`, the components of `X_Ω` are already distinguished over a
  finite intermediate field `E`: closure of image under `X_Ω ⟶ X_F` is a bijection on
  irreducible components for every intermediate field `F ⊇ E`. On a finite affine cover of `X` by
  charts `Spec A`, this is the finite affine descent
  `PrimeSpectrum.exists_finiteDimensional_forall_bijOn_closure_image_comap_irreducibleComponents`,
  since the base changes of `Spec A` are the charts `Spec (F ⊗[K] A)` of `X_F`; the chartwise
  bijections glue by
  `AlgebraicGeometry.Scheme.Hom.bijOn_closure_image_irreducibleComponents_iff_of_isPullback`.
* Take `Ω` to be the separable closure of `K`. Over `Ω` every irreducible component is
  geometrically irreducible
  (`TauCeti.AlgebraicGeometry.bijOn_preimage_irreducibleComponents_of_isSepClosed`). For a field
  `M ⊇ E`, choose a field `N` containing both `M` and `Ω` over `E`; the preimage of a component of
  `X_E` in `X_N` is a component, because `X_N ⟶ X_E` factors through `X_Ω`, so its preimage in
  `X_M` is irreducible, and `X_M ⟶ X_E` is surjective.

## Main results

* `Scheme.Hom.exists_finiteDimensional_forall_bijOn_closure_image_irreducibleComponents`: the
  components over an algebraic extension are distinguished over a finite intermediate field.
* `Scheme.Hom.exists_forall_bijOn_preimage_irreducibleComponents`: the irreducible components
  become geometrically irreducible over a finite separable extension.

## References

* The Stacks Project, Section 33.8, *Geometrically irreducible schemes*, Lemmas 33.8.15–16.
-/

public section

open CategoryTheory Limits Set
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- **Components over an algebraic extension are distinguished over a finite subextension.**
Let `f : X ⟶ Spec K` be quasi-compact and locally of finite type, and let `L / K` be algebraic.
There is a finite intermediate field `E` such that for every intermediate field `F ⊇ E`, every
base change `X_F` of `X` to `F` and every base change `X_L ⟶ X_F` of `Spec L ⟶ Spec F`, closure
of image is a bijection from the irreducible components of `X_L` onto those of `X_F`. -/
theorem exists_finiteDimensional_forall_bijOn_closure_image_irreducibleComponents
    {K L : Type u} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [QuasiCompact f] [LocallyOfFiniteType f] :
    ∃ E : IntermediateField K L, FiniteDimensional K E ∧
      ∀ F : IntermediateField K L, E ≤ F →
        ∀ {XF XL : Scheme.{u}} {pF : XF ⟶ X} {fF : XF ⟶ Spec (.of F)} {g : XL ⟶ XF}
          {fL : XL ⟶ Spec (.of L)},
          IsPullback pF fF f (Spec.algebraMap K F) →
          IsPullback g fL fF (Spec.algebraMap F L) →
          BijOn (fun Z ↦ closure (g '' Z)) (irreducibleComponents XL)
            (irreducibleComponents XF) := by
  obtain ⟨ι, _, A, _, _, _, φ, _, hφ, hcov⟩ := exists_finite_affine_charts f
  obtain ⟨E, hE, hbij⟩ :=
    PrimeSpectrum.exists_finiteDimensional_forall_bijOn_closure_image_comap_irreducibleComponents
      (K := K) (L := L) A
  refine ⟨E, hE, fun F hF XF XL pF fF g fL HF HL ↦ ?_⟩
  have HFL : IsPullback (g ≫ pF) fL f (Spec.algebraMap K L) := by
    have := HL.paste_horiz HF
    rwa [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq] at this
  -- The charts `Spec (F ⊗[K] A i)` of `X_F` and `Spec (L ⊗[K] A i)` of `X_L`, the base changes
  -- of the charts `Spec (A i)` of `X`.
  have hT' (S : Type u) [Field S] [Algebra K S] (i : ι) : IsPullback
      (Spec.map (CommRingCat.ofHom (S := S ⊗[K] A i) Algebra.TensorProduct.includeLeftRingHom))
      (Spec.map (CommRingCat.ofHom (S := S ⊗[K] A i) Algebra.TensorProduct.includeRight.toRingHom))
      (Spec.algebraMap K S) (φ i ≫ f) := by
    rw [hφ]
    exact isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct K S (A i))
  have sqF (i : ι) := IsPullback.of_right' (hT' F i) HF.flip
  have sqL (i : ι) := IsPullback.of_right' (hT' L i) HFL.flip
  let 𝒱 : XF.OpenCover := Cover.mkOfCovers ι _
    (fun i ↦ HF.flip.lift _ _ ((hT' F i).w.trans (Category.assoc _ _ _).symm))
    (fun x ↦ by
      obtain ⟨i, y, hy⟩ := hcov (pF x)
      obtain ⟨z, hz, -⟩ := exists_preimage_of_isPullback (sqF i) x y hy.symm
      exact ⟨i, z, hz⟩)
    (fun i ↦ MorphismProperty.of_isPullback (sqF i).flip inferInstance)
  -- The base change of `X_L ⟶ X_F` to the `i`-th chart is `Spec (L ⊗[K] A i) ⟶ Spec (F ⊗[K] A i)`.
  let m (i : ι) := Algebra.TensorProduct.map F.val (AlgHom.id K (A i))
  have hl (i : ι) : Spec.map (CommRingCat.ofHom (m i).toRingHom) ≫
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) =
        Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫
          Spec.algebraMap F L := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_))
    simp [m]
  have hr (i : ι) : Spec.map (CommRingCat.ofHom (m i).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (S := F ⊗[K] A i)
        Algebra.TensorProduct.includeRight.toRingHom) =
        Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) := by
    rw [← Spec.map_comp]
    refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_))
    simp [m]
  have hp (i : ι) : IsPullback
      (HFL.flip.lift _ _ ((hT' L i).w.trans (Category.assoc _ _ _).symm))
      (Spec.map (CommRingCat.ofHom (m i).toRingHom)) g (𝒱.f i) := by
    refine IsPullback.of_bot ?_ (HF.hom_ext ?_ ?_) (sqF i)
    · rw [hr]
      exact sqL i
    · simp only [𝒱, Cover.mkOfCovers_f, Category.assoc, IsPullback.lift_snd, reassoc_of% hr]
    · simp only [𝒱, Cover.mkOfCovers_f, Category.assoc, HL.w, IsPullback.lift_fst_assoc,
        IsPullback.lift_fst]
      exact (hl i).symm
  exact (g.bijOn_closure_image_irreducibleComponents_iff_of_isPullback 𝒱 hp).mpr
    fun i ↦ hbij F hF i

/-- **The irreducible components become geometrically irreducible over a finite separable
extension.** Let `f : X ⟶ Spec K` be quasi-compact and locally of finite type. There is a finite
separable extension `L / K` such that for every further field extension `F / L`, every base
change `X_F` of `X` to `F`, every field extension `M / F` and every base change
`h : X_M ⟶ X_F` of `Spec M ⟶ Spec F`, the map `Z ↦ h ⁻¹' Z` is a bijection from the
irreducible components of `X_F` onto those of `X_M`. -/
theorem exists_forall_bijOn_preimage_irreducibleComponents {K : Type u} [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [QuasiCompact f] [LocallyOfFiniteType f] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Module.Finite K L)
      (_ : Algebra.IsSeparable K L),
      ∀ (F : Type u) [Field F] [Algebra K F] [Algebra L F] [IsScalarTower K L F]
        {XF : Scheme.{u}} {pF : XF ⟶ X} {fF : XF ⟶ Spec (.of F)},
        IsPullback pF fF f (Spec.algebraMap K F) →
        ∀ (M : Type u) [Field M] [Algebra F M] {XM : Scheme.{u}} {h : XM ⟶ XF}
          {fM : XM ⟶ Spec (.of M)}, IsPullback h fM fF (Spec.algebraMap F M) →
          BijOn (h ⁻¹' ·) (irreducibleComponents XF) (irreducibleComponents XM) := by
  let Ω := SeparableClosure K
  obtain ⟨E, hE, hbij⟩ :=
    f.exists_finiteDimensional_forall_bijOn_closure_image_irreducibleComponents (L := Ω)
  have : Algebra.IsSeparable K E := Algebra.isSeparable_tower_bot_of_isSeparable K E Ω
  have hgeom {XL : Scheme.{u}} {pL : XL ⟶ X} {fL : XL ⟶ Spec (.of E)}
      (HL : IsPullback pL fL f (Spec.algebraMap K E))
      (M : Type u) [Field M] [Algebra E M] {XM : Scheme.{u}} {h : XM ⟶ XL}
      {fM : XM ⟶ Spec (.of M)} (HM : IsPullback h fM fL (Spec.algebraMap E M)) :
      BijOn (h ⁻¹' ·) (irreducibleComponents XL) (irreducibleComponents XM) := by
    -- Over the separable closure `Ω`, preimage is a bijection on components, `X_Ω ⟶ X_E` being
    -- flat with the components of `X_Ω` distinguished over `E`.
    let gΩ := pullback.fst fL (Spec.algebraMap E Ω)
    have : Flat (Spec.algebraMap E Ω) := by
      rw [Flat.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]
      infer_instance
    have hΩ : BijOn (gΩ ⁻¹' ·) (irreducibleComponents XL) (irreducibleComponents _) :=
      (Flat.generalizingMap gΩ).bijOn_preimage_irreducibleComponents
        (hbij E le_rfl HL (IsPullback.of_hasPullback _ _))
    -- A field `N` containing both `M` and `Ω` over `E`.
    let d := TauCeti.Algebra.TensorProduct.commonOverfield E M Ω
    let N := d.Ω
    let _ : Algebra E N := d.algebraOmega
    let _ : Algebra M N := d.algebraKΩ
    have : IsScalarTower E M N := d.isScalarTower
    let _ : Algebra Ω N := d.right.toRingHom.toAlgebra
    -- Keep the common overfield's scalar action rather than restriction through `Ω`.
    let _ : SMul E N := d.algebraOmega.toSMul
    have : IsScalarTower E Ω N := .of_algHom d.right
    have hMΩ : Spec.algebraMap M N ≫ Spec.algebraMap E M =
        Spec.algebraMap Ω N ≫ Spec.algebraMap E Ω := by
      simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
    -- `X_N ⟶ X_M` is surjective, and `X_N ⟶ X_E` factors through `X_Ω` as a base change of
    -- `Spec N ⟶ Spec Ω`.
    let hN := pullback.fst fM (Spec.algebraMap M N)
    have HN := (IsPullback.of_hasPullback fM (Spec.algebraMap M N)).paste_horiz HM
    rw [hMΩ] at HN
    obtain ⟨ℓ, HΩ, hℓ⟩ :
        ∃ ℓ : pullback fM (Spec.algebraMap M N) ⟶ pullback fL (Spec.algebraMap E Ω),
          IsPullback ℓ (pullback.snd _ _) (pullback.snd _ _) (Spec.algebraMap Ω N) ∧
            ℓ ≫ gΩ = hN ≫ h :=
      ⟨_, IsPullback.of_right' HN (IsPullback.of_hasPullback _ _), IsPullback.lift_fst _ _ _ _⟩
    have hNΩ := TauCeti.AlgebraicGeometry.bijOn_preimage_irreducibleComponents_of_isSepClosed HΩ
    have : Surjective h := MorphismProperty.of_isPullback HM.flip inferInstance
    refine h.surjective.bijOn_preimage_irreducibleComponents h.continuous fun Z hZ ↦ ?_
    -- The preimage of `Z` in `X_N` is a component, so its image in `X_M` is irreducible.
    have hpre : hN ⁻¹' (h ⁻¹' Z) = ℓ ⁻¹' (gΩ ⁻¹' Z) := by
      ext x
      simp only [Set.mem_preimage]
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hℓ]
    rw [← image_preimage_eq (h ⁻¹' Z) hN.surjective, hpre]
    exact (hNΩ.mapsTo (hΩ.mapsTo hZ)).1.image _ hN.continuous.continuousOn
  refine ⟨E, inferInstance, inferInstance, hE, inferInstance, ?_⟩
  intro F _ _ _ _ XF pF fF HF M _ _ XM h fM HM
  -- Compare both extensions to the same base change over `E`, then cancel its component
  -- bijection to obtain the component bijection over `F`.
  have HKF : Spec.algebraMap K F = Spec.algebraMap E F ≫ Spec.algebraMap K E := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  rw [HKF] at HF
  have HE := IsPullback.of_hasPullback f (Spec.algebraMap K E)
  have HFE := IsPullback.of_right' HF HE
  have hF := hgeom HE F HFE
  let _ : Algebra E M := ((algebraMap F M).comp (algebraMap E F)).toAlgebra
  have : IsScalarTower E F M := .of_algebraMap_eq' rfl
  have HME := HM.paste_horiz HFE
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq] at HME
  have hM := hgeom HE M HME
  have hc : BijOn ((h ⁻¹' ·) ∘ (HE.lift pF (fF ≫ Spec.algebraMap E F) HF.w ⁻¹' ·))
      (irreducibleComponents _) (irreducibleComponents XM) := by
    convert hM using 1
    ext Z x
    simp only [Function.comp_apply, Set.mem_preimage, Scheme.Hom.comp_apply]
  simpa only [hF.image_eq] using (Set.bijOn_comp_iff hF.injOn).mp hc

end AlgebraicGeometry.Scheme.Hom
