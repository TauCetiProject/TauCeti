/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.InjectivelyTrivial

/-!
# The Auslander–Reiten pairing on Hom cocycles

For a map `f : P₁ → P₀` between finite projective modules, let `Z` be the maps
`P₁ → N` vanishing on `ker f`, and let `B` be the maps obtained by precomposition
with `f`. The Nakayama Hom pairing induces a surjection

`Hom_A(N, D Tr(f)) → D (Z / B)`.

Its kernel consists exactly of maps extending across an embedding of `N` into an
injective module. Thus quotienting the Hom space by maps through injectives gives
the dual of the cocycle quotient. Unlike the full Hom cokernel, `Z / B` imposes the
cocycle condition required for a projective presentation with nonzero kernel.
The pairing is defined over a commutative ring; surjectivity and the kernel criterion
use a field. No minimality or finite-dimensionality of the algebra or `N` is required.

In presentation-level Auslander–Reiten duality, identifying the cocycle quotient
with `Ext¹` gives a pairing between extension classes and maps into the translate
modulo maps through injectives.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section IV.2.

The construction uses `TauCeti.nakayamaHomEquiv` and
`LinearMap.auslanderReitenTranslateEquivKerNakayama`.
-/

public section

namespace LinearMap

open TauCeti

universe u v w z t s

variable {k : Type u} {A : Type v} [Ring A]
  {P₀ : Type w} {P₁ : Type z} {N : Type t}
  [AddCommGroup P₀] [Module A P₀] [Module.Finite A P₀] [Module.Projective A P₀]
  [AddCommGroup P₁] [Module A P₁] [Module.Finite A P₁] [Module.Projective A P₁]
  [AddCommGroup N] [Module A N]

section CommRing

variable [CommRing k] [Algebra k A] [Module k N] [IsScalarTower k A N]

private theorem translate_functional_mem_annihilator (f : P₁ →ₗ[A] P₀)
    (g : N →ₗ[A] AuslanderReitenTranslate k f) :
    (nakayamaHomEquiv k A P₁ N).symm ((auslanderReitenTranslateToNakayama f).comp g) ∈
      (range (f.lcomp k N)).dualAnnihilator := by
  rw [← ker_dualMap_eq_dualAnnihilator_range, mem_ker]
  apply (nakayamaHomEquiv k A P₀ N).injective
  rw [nakayamaHomEquiv_dualMap_lcomp, map_zero]
  ext n ψ
  simp [(exact_auslanderReitenTranslateToNakayama_nakayamaMap f).apply_apply_eq_zero]

/-- The Auslander–Reiten pairing restricts a translate Hom functional to the Hom
cocycles and descends it modulo the coboundaries. -/
noncomputable def auslanderReitenCocyclePairing (f : P₁ →ₗ[A] P₀) :
    (N →ₗ[A] AuslanderReitenTranslate k f) →ₗ[k]
      Module.Dual k
        (ker ((ker f).subtype.lcomp k N) ⧸
          (range (f.lcomp k N)).comap (ker ((ker f).subtype.lcomp k N)).subtype) := by
  let Z := ker ((ker f).subtype.lcomp k N)
  let B := (range (f.lcomp k N)).comap Z.subtype
  let χ := (nakayamaHomEquiv k A P₁ N).symm.toLinearMap.comp
    ((auslanderReitenTranslateToNakayama f).compRight k)
  exact B.dualCopairing.comp ((Z.dualRestrict.comp χ).codRestrict B.dualAnnihilator
    fun g ↦ by
      rw [Submodule.mem_dualAnnihilator]
      intro h hh
      simpa [χ] using
        (Submodule.mem_dualAnnihilator _).mp
          (translate_functional_mem_annihilator f g) h hh)

/-- Evaluation of the pairing on a cocycle class is restriction of the Nakayama
Hom functional. This characterizes the pairing without unfolding its construction. -/
@[simp]
theorem auslanderReitenCocyclePairing_apply_mk (f : P₁ →ₗ[A] P₀)
    (g : N →ₗ[A] AuslanderReitenTranslate k f)
    (h : ker ((ker f).subtype.lcomp k N)) :
    auslanderReitenCocyclePairing f g (Submodule.Quotient.mk h) =
      (nakayamaHomEquiv k A P₁ N).symm
        ((auslanderReitenTranslateToNakayama f).comp g) h := by
  simp only [auslanderReitenCocyclePairing, comp_apply, Submodule.dualCopairing_apply]
  -- The codomain restriction stores exactly the restricted functional.
  rfl

end CommRing

section Field

variable [Field k] [Algebra k A] [Module k N] [IsScalarTower k A N]

/-- The additive group inherited from the dual, made available locally so that
nested quotient instance synthesis can find it in the public quotient signatures. -/
local instance (f : P₁ →ₗ[A] P₀) : AddCommGroup (AuslanderReitenTranslate k f) :=
  inferInstanceAs (AddCommGroup (Module.Dual k (AuslanderReitenTranspose f)))

/-- Every functional on Hom cocycles modulo coboundaries is obtained by pairing
with a map into the Auslander–Reiten translate. -/
theorem auslanderReitenCocyclePairing_surjective (f : P₁ →ₗ[A] P₀) :
    Function.Surjective (auslanderReitenCocyclePairing (k := k) (N := N) f) := by
  intro φ
  let Z := ker ((ker f).subtype.lcomp k N)
  let B := (range (f.lcomp k N)).comap Z.subtype
  let ψ := B.mkQ.dualMap φ
  let χ := Subspace.dualLift Z ψ
  have hχ : χ ∈ (range (f.lcomp k N)).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro h hh
    have hZ : h ∈ Z := by
      obtain ⟨a, rfl⟩ := hh
      apply mem_ker.mpr
      ext x
      simp [lcomp_apply', mem_ker.mp x.property]
    let z : Z := ⟨h, hZ⟩
    have hz : z ∈ B := hh
    calc
      χ h = ψ z := Subspace.dualLift_of_mem hZ
      _ = 0 := by
        simp only [ψ, dualMap_apply, Submodule.mkQ_apply]
        rw [(Submodule.Quotient.mk_eq_zero B).mpr hz, map_zero]
  let H := nakayamaHomEquiv k A P₁ N χ
  have hH : f.nakayamaMap.comp H = 0 := by
    have hzero : (f.lcomp k N).dualMap χ = 0 := by
      rwa [← ker_dualMap_eq_dualAnnihilator_range, mem_ker] at hχ
    simpa only [H, nakayamaHomEquiv_dualMap_lcomp, map_zero] using
      congrArg (nakayamaHomEquiv k A P₀ N) hzero
  let g := (auslanderReitenTranslateEquivKerNakayama f).symm.toLinearMap.comp
    (H.codRestrict (ker f.nakayamaMap) fun n ↦ mem_ker.mpr (LinearMap.congr_fun hH n))
  have hg : (auslanderReitenTranslateToNakayama f).comp g = H := by
    ext n ξ
    simp [g, auslanderReitenTranslateToNakayama_apply]
  refine ⟨g, ?_⟩
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ h =>
    simp [auslanderReitenCocyclePairing_apply_mk, hg, H, χ, ψ, Z, dualMap_apply]

/-- A map has zero cocycle pairing exactly when its Nakayama functional is in the
image of dual restriction to the kernel of the presenting arrow. -/
theorem auslanderReitenCocyclePairing_eq_zero_iff (f : P₁ →ₗ[A] P₀)
    (g : N →ₗ[A] AuslanderReitenTranslate k f) :
    auslanderReitenCocyclePairing f g = 0 ↔
      (nakayamaHomEquiv k A P₁ N).symm ((auslanderReitenTranslateToNakayama f).comp g) ∈
        range (((ker f).subtype.lcomp k N).dualMap) := by
  rw [range_dualMap_eq_dualAnnihilator_ker, Submodule.mem_dualAnnihilator]
  constructor
  · intro hg h hh
    simpa only [auslanderReitenCocyclePairing_apply_mk, zero_apply] using
      LinearMap.congr_fun hg (Submodule.Quotient.mk ⟨h, hh⟩)
  · intro hg
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ h => simpa using hg h h.property

/-- The kernel of the Auslander–Reiten cocycle pairing consists exactly of maps
extending across any fixed embedding into an injective module. -/
theorem auslanderReitenCocyclePairing_eq_zero_iff_exists_extension
    {I : Type s} [AddCommGroup I] [Module A I] [Module k I] [IsScalarTower k A I]
    [Small.{s} A] [Module.Injective A I]
    (f : P₁ →ₗ[A] P₀) (j : N →ₗ[A] I) (hj : Function.Injective j)
    (g : N →ₗ[A] AuslanderReitenTranslate k f) :
    auslanderReitenCocyclePairing f g = 0 ↔
      ∃ h : I →ₗ[A] AuslanderReitenTranslate k f, h.comp j = g := by
  rw [auslanderReitenCocyclePairing_eq_zero_iff,
    auslanderReitenTranslate_exists_extension_iff f j hj]

/-- An embedding into an injective module computes the quotient of translate Hom
by injectively trivial maps. The cocycle pairing identifies this quotient with the
dual of Hom cocycles modulo coboundaries. -/
noncomputable def auslanderReitenCocycleQuotientEquiv
    {I : Type s} [AddCommGroup I] [Module A I] [Module k I] [IsScalarTower k A I]
    [Small.{s} A] [Module.Injective A I]
    (f : P₁ →ₗ[A] P₀) (j : N →ₗ[A] I) (hj : Function.Injective j) :
    ((N →ₗ[A] AuslanderReitenTranslate k f) ⧸
      range (j.lcomp k (AuslanderReitenTranslate k f))) ≃ₗ[k]
      Module.Dual k
        (ker ((ker f).subtype.lcomp k N) ⧸
          (range (f.lcomp k N)).comap (ker ((ker f).subtype.lcomp k N)).subtype) := by
  have hker : ker (auslanderReitenCocyclePairing (k := k) (N := N) f) =
      range (j.lcomp k (AuslanderReitenTranslate k f)) := by
    ext g
    rw [mem_ker, auslanderReitenCocyclePairing_eq_zero_iff_exists_extension f j hj,
      mem_range]
    simp only [LinearMap.lcomp_apply']
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans
    ((auslanderReitenCocyclePairing (k := k) (N := N) f).quotKerEquivOfSurjective
      (auslanderReitenCocyclePairing_surjective (k := k) (N := N) f))

/-- On a representative, quotient duality is the cocycle pairing. -/
@[simp]
theorem auslanderReitenCocycleQuotientEquiv_mk
    {I : Type s} [AddCommGroup I] [Module A I] [Module k I] [IsScalarTower k A I]
    [Small.{s} A] [Module.Injective A I]
    (f : P₁ →ₗ[A] P₀) (j : N →ₗ[A] I) (hj : Function.Injective j)
    (g : N →ₗ[A] AuslanderReitenTranslate k f) :
    auslanderReitenCocycleQuotientEquiv f j hj (Submodule.Quotient.mk g) =
      auslanderReitenCocyclePairing f g := by
  simp [auslanderReitenCocycleQuotientEquiv]

/-- Inverse quotient duality returns the class of any map giving the functional. -/
@[simp]
theorem auslanderReitenCocycleQuotientEquiv_symm_pairing
    {I : Type s} [AddCommGroup I] [Module A I] [Module k I] [IsScalarTower k A I]
    [Small.{s} A] [Module.Injective A I]
    (f : P₁ →ₗ[A] P₀) (j : N →ₗ[A] I) (hj : Function.Injective j)
    (g : N →ₗ[A] AuslanderReitenTranslate k f) :
    (auslanderReitenCocycleQuotientEquiv f j hj).symm (auslanderReitenCocyclePairing f g) =
      Submodule.Quotient.mk g := by
  apply (auslanderReitenCocycleQuotientEquiv f j hj).injective
  simp

end Field

end LinearMap
