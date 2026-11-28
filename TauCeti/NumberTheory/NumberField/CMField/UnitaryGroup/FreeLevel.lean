/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.AdelicFrame
public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.PrincipalLevel
public import TauCeti.RepresentationTheory.Induction.Mackey.Subgroup
import TauCeti.NumberTheory.NumberField.UnitaryCongruence
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Unitary
import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Basic

/-!
# Free principal levels on definite framed Hermitian spaces

For a definite Hermitian space over a CM field `E`, all class stabilizers at a level contained
in the principal level of `I` are trivial if `Norm(I) > (2n)^[E:ℚ]`, where `n` is the rank.
The infinite frame conjugates each complex image of a rational isometry to a unitary matrix.
The finite frame transfers the principal-level congruence to the rational isometry. Thus the
trace congruence criterion applies even when the rational Gram matrix is not the identity.
Trivial stabilizers remove the stabilizer denominators in class-sum pairings.

The class-stabilizer calculation follows `New.Variety.classAut_eq_bot` in
`grh/src/Lib/Shimura/HeckeTower/HeckeData.lean` of [lsernau/grh-lean](https://github.com/lsernau/grh-lean)
(revision `72fead1`). The congruence bound extends the trace argument of
`NumberField.IsCMField.comap_map_conj_eq_bot` from the standard form to definite framed forms.
-/

public section

open IsDedekindDomain Matrix NumberField Module
open scoped NumberField.AdeleRing

namespace TauCeti.FramedHermitianSpace

universe u

variable {E : Type u} [Field E] [NumberField E] [IsCMField E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem exists_conj_map_mem_unitaryGroup (V : FramedHermitianSpace E (1 : ι → ℤˣ))
    (γ : unitaryGroupOf V.gram) (φ : E →+* ℂ) :
    ∃ u : GL ι ℂ, ((↑u⁻¹ : Matrix ι ι ℂ) * ((γ : GL ι E) : Matrix ι ι E).map φ *
      (u : Matrix ι ι ℂ)) ∈ unitaryGroup ι ℂ := by
  let w := InfinitePlace.mk φ
  let f : InfiniteAdeleRing E →+* ℂ :=
    (InfinitePlace.Completion.extensionEmbedding w).comp (Pi.evalRingHom _ w)
  have hf (x : InfiniteAdeleRing E) : f (star x) = star (f x) :=
    InfiniteAdeleRing.extensionEmbedding_star_apply x w
  have hf' : f.comp (algebraMap E (InfiniteAdeleRing E)) = w.embedding := by
    ext x
    -- Expose the coordinate of the product ring behind `InfiniteAdeleRing` for the rewrite.
    change InfinitePlace.Completion.extensionEmbedding w
      ((algebraMap E (InfiniteAdeleRing E) x) w) = w.embedding x
    rw [InfiniteAdeleRing.algebraMap_apply, InfinitePlace.Completion.extensionEmbedding_coe]
    rfl
  have h (g : InfiniteAdeleRing E →+* ℂ) (hg : ∀ x, g (star x) = star (g x)) :
      ∃ u : GL ι ℂ, ((↑u⁻¹ : Matrix ι ι ℂ) *
        ((γ : GL ι E) : Matrix ι ι E).map (g.comp (algebraMap E (InfiniteAdeleRing E))) *
        (u : Matrix ι ι ℂ)) ∈ unitaryGroup ι ℂ := by
    refine ⟨GeneralLinearGroup.map g V.frame.1, ?_⟩
    have hγ := (V.infiniteRationalEmbedding γ).property
    simp only [infiniteAdelicUnitaryGroup, Pi.one_apply, Units.val_one, Int.cast_one,
      diagonal_one, unitaryGroupOf_one] at hγ
    have hu := map_mem_unitary g hg (mem_unitarySubgroup_GL_iff_mem_unitaryGroup.mp hγ)
    have hmap : GeneralLinearGroup.map g (V.infiniteRationalEmbedding γ : GL ι _) =
        (GeneralLinearGroup.map g V.frame.1)⁻¹ *
          GeneralLinearGroup.map (g.comp (algebraMap E (InfiniteAdeleRing E))) (γ : GL ι E) *
          GeneralLinearGroup.map g V.frame.1 := by
      simp only [coe_infiniteRationalEmbedding, map_mul, map_inv,
        GeneralLinearGroup.map_comp, MonoidHom.comp_apply]
    have hval {R : Type u} [CommRing R] (e : R →+* ℂ) (a : GL ι R) :
        (↑(GeneralLinearGroup.map e a) : Matrix ι ι ℂ) = a.val.map e :=
      Matrix.ext fun i j ↦ GeneralLinearGroup.map_apply _ i j _
    rw [← hval, hmap] at hu
    simpa only [Units.val_mul, hval] using hu
  rcases InfinitePlace.embedding_mk_eq φ with he | he
  · have he' : w.embedding = φ := he
    simpa only [hf', he'] using h f hf
  · have hc : star w.embedding = φ := (congrArg ComplexEmbedding.conjugate he).trans
      (ComplexEmbedding.involutive_conjugate E φ)
    have hg' : (star f).comp (algebraMap E (InfiniteAdeleRing E)) = φ := by
      ext x
      simpa only [RingHom.comp_apply, RingHom.star_apply] using
        congrArg (fun a : E →+* ℂ ↦ a x) ((congrArg star hf').trans hc)
    simpa only [hg'] using h (star f) (fun x ↦ by simp only [RingHom.star_apply, hf])

/-- Every class stabilizer at a subgroup of a sufficiently deep principal level of a definite
framed space is trivial. The modulus can be any ideal with absolute norm exceeding
`(2 * card ι) ^ finrank ℚ E`. -/
theorem mackeySubgroup_eq_bot_of_le_principalUnitaryLevel
    (V : FramedHermitianSpace E (1 : ι → ℤˣ)) {I : Ideal (𝓞 E)}
    (hI : (2 * Fintype.card ι) ^ finrank ℚ E < Ideal.absNorm I)
    {J : Subgroup (finiteAdelicUnitaryGroup E ι)} (hJ : J ≤ principalUnitaryLevel E ι I)
    (g : finiteAdelicUnitaryGroup E ι) : mackeySubgroup g J V.finiteRationalPoints = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun z hz ↦ ?_
  obtain ⟨hz, hg⟩ := mem_mackeySubgroup_iff.mp hz
  obtain ⟨γ, hγ⟩ := V.mem_finiteRationalPoints_iff.mp hz
  obtain ⟨k, hk, hcong⟩ := mem_principalUnitaryLevel_iff.mp (hJ hg)
  let x := V.frame.2 * (g : GL ι 𝔸ᶠ[E])
  have hconj : x⁻¹ * GeneralLinearGroup.map (algebraMap E 𝔸ᶠ[E]) γ * x =
      FiniteAdeleRing.integralGL E ι k := by
    calc
      _ = (g : GL ι 𝔸ᶠ[E])⁻¹ * (z : GL ι 𝔸ᶠ[E]) * (g : GL ι 𝔸ᶠ[E]) := by
        rw [← hγ]
        simp [x, mul_assoc]
      _ = _ := hk.symm
  have hone : ((γ : GL ι E) : Matrix ι ι E) = 1 :=
    eq_one_of_conj_sub_one_mem_completedIdeal_of_archimedean_unitary
      (γ := (γ : GL ι E).val) (V.exists_conj_map_mem_unitaryGroup γ) hI x fun i j ↦ by
        refine ⟨_, hcong i j, ?_⟩
        have hmap : (↑(GeneralLinearGroup.map (algebraMap E 𝔸ᶠ[E]) (γ : GL ι E)) :
            Matrix ι ι 𝔸ᶠ[E]) = (γ : GL ι E).val.map (algebraMap E 𝔸ᶠ[E]) :=
          Matrix.ext fun a b ↦ GeneralLinearGroup.map_apply _ a b _
        have hentry := congrArg (fun u : GL ι 𝔸ᶠ[E] ↦ (u : Matrix ι ι 𝔸ᶠ[E]) i j) hconj
        simp only [Units.val_mul, hmap, FiniteAdeleRing.integralGL_apply] at hentry
        rw [Matrix.sub_apply, Subalgebra.coe_sub, hentry]
        congr 1
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hγ1 : γ = 1 := Subtype.ext (Units.ext hone)
  exact Subtype.ext (by simpa [hγ1] using hγ.symm)

end TauCeti.FramedHermitianSpace
