/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import TauCeti.Algebra.Module.LocalizedModule.Lift
public import TauCeti.RepresentationTheory.BaseChange

/-!
# Lattices with equivalent localizations

Let `ρ` and `σ` be representations of a monoid `G` on finitely generated `R`-modules `V` and `W`,
and let `A` be the localization of `R` at a submonoid `S` whose elements act injectively on `V`
and on `W`. If the scalar extensions `A ⊗[R] V` and `A ⊗[R] W` are equivalent representations,
then `V` and `W` are equivalent up to a scalar of `S`: there are intertwining maps `f : V → W` and
`f' : W → V` and an `s ∈ S` with `f' ∘ f = s • id` and `f ∘ f' = s • id`.

The maps are obtained by clearing denominators. The equivalence `e` restricted to `V ⊆ A ⊗[R] V`
takes values with denominators in `S`, and because `V` is finitely generated a single `s ∈ S`
clears all of them (`Module.Finite.exists_lift_of_isLocalizedModule_of_injective`), so that
`s • e` maps `V` into `W`. Intertwining is inherited from `e`, since `W` embeds in `A ⊗[R] W`.

For representations over `ℤ`, with `S` the nonzero integers and `A = ℚ`, this says that two
representations on finitely generated torsion-free `ℤ`-modules with equivalent
rationalizations are related by an injective intertwining map with finite cokernel. This is the
lattice input to the comparison of the reductions modulo a prime `ℓ` of two `ℤ[G]`-lattices
with isomorphic rationalizations: the reductions need not be isomorphic, but the finite-index
embedding forces their classes in the Grothendieck group of `𝔽_ℓ[G]` to agree.

## Main results

* `Representation.Equiv.exists_intertwiningMap_comp_eq_smul`: representations on `S`-torsion-free
  finitely generated modules with equivalent localizations are equivalent up to a scalar of `S`.
* `Representation.Equiv.exists_injective_finite_quotient_range`: two representations on finitely
  generated torsion-free `ℤ`-modules with equivalent rationalizations admit an injective
  intertwining map from one to the other with finite cokernel.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  §VII.3, (7.3.3).
* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed. (2006), Chapter I, Lemma 2.12.
-/

public section

namespace TauCeti

open TensorProduct

section Localization

variable {R : Type*} [CommSemiring R] {A : Type*} [CommSemiring A] [Algebra R A]
  {G : Type*} [Monoid G] {V W : Type*} [AddCommMonoid V] [Module R V] [AddCommMonoid W]
  [Module R W]
  {ρ : Representation R G V} {σ : Representation R G W}

/-- Two representations on finitely generated modules on which `S` acts injectively, whose
scalar extensions to the localization `A` of `R` at `S` are equivalent, are equivalent up to a
scalar of `S`: there are intertwining maps `f : V → W` and `f' : W → V` and `s ∈ S` with
`f' ∘ f = s • id` and `f ∘ f' = s • id`. -/
theorem _root_.Representation.Equiv.exists_intertwiningMap_comp_eq_smul
    (e : (Representation.baseChange A ρ).Equiv (Representation.baseChange A σ))
    (S : Submonoid R) [IsLocalization S A] [Module.Finite R V] [Module.Finite R W]
    (hV : ∀ s : S, IsSMulRegular V (s : R)) (hW : ∀ s : S, IsSMulRegular W (s : R)) :
    ∃ (f : ρ.IntertwiningMap σ) (f' : σ.IntertwiningMap ρ) (s : S),
      (∀ v, f' (f v) = (s : R) • v) ∧ ∀ w, f (f' w) = (s : R) • w := by
  set iV := TensorProduct.mk R A V 1
  set iW := TensorProduct.mk R A W 1
  have hiV : Function.Injective iV := (IsLocalizedModule.injective_iff_isRegular S iV).mpr hV
  have hiW : Function.Injective iW := (IsLocalizedModule.injective_iff_isRegular S iW).mpr hW
  -- Clear the denominators of `e` on `V` and of `e.symm` on `W`.
  have : IsLocalizedModule S (iV.restrictScalars R) := inferInstanceAs (IsLocalizedModule S iV)
  have : IsLocalizedModule S (iW.restrictScalars R) := inferInstanceAs (IsLocalizedModule S iW)
  obtain ⟨h, s, hh⟩ := Module.Finite.exists_lift_of_isLocalizedModule_of_injective S hiW
    (e.toLinearMap.restrictScalars R ∘ₗ iV)
  obtain ⟨h', t, hh'⟩ := Module.Finite.exists_lift_of_isLocalizedModule_of_injective S hiV
    (e.symm.toLinearMap.restrictScalars R ∘ₗ iW)
  replace hh (v : V) : iW (h v) = (s : R) • e (iV v) := by
    simpa [Submonoid.smul_def] using congr($hh v)
  replace hh' (w : W) : iV (h' w) = (t : R) • e.symm (iW w) := by
    simpa [Submonoid.smul_def] using congr($hh' w)
  -- The inclusions `V → A ⊗[R] V` and `W → A ⊗[R] W` are equivariant.
  have hρ (g : G) (v : V) : iV (ρ g v) = Representation.baseChange A ρ g (iV v) := by
    simp [iV]
  have hσ (g : G) (w : W) : iW (σ g w) = Representation.baseChange A σ g (iW w) := by
    simp [iW]
  have he (g : G) (x : A ⊗[R] V) : e (Representation.baseChange A ρ g x) =
      Representation.baseChange A σ g (e x) := by
    simpa using Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g x
  have he' (g : G) (y : A ⊗[R] W) : e.symm (Representation.baseChange A σ g y) =
      Representation.baseChange A ρ g (e.symm y) := by
    simpa using Representation.IntertwiningMap.isIntertwining _ _ e.symm.toIntertwiningMap g y
  have hint (g : G) (v : V) : h (ρ g v) = σ g (h v) := hiW <| by
    rw [hh, hσ, hh, hρ, he]
    simp [LinearMap.map_smul_of_tower]
  have hint' (g : G) (w : W) : h' (σ g w) = ρ g (h' w) := hiV <| by
    rw [hh', hρ, hh', hσ, he']
    simp [LinearMap.map_smul_of_tower]
  have hcomp (v : V) : h' (h v) = ((s * t : S) : R) • v := hiV <| by
    rw [hh', hh]
    simp [LinearMapClass.map_smul_of_tower e.symm, mul_smul, smul_comm (t : R) (s : R)]
  have hcomp' (w : W) : h (h' w) = ((s * t : S) : R) • w := hiW <| by
    rw [hh, hh']
    simp [LinearMapClass.map_smul_of_tower e, mul_smul]
  exact ⟨⟨h, fun g ↦ LinearMap.ext (hint g)⟩, ⟨h', fun g ↦ LinearMap.ext (hint' g)⟩, s * t,
    by simpa using hcomp, by simpa using hcomp'⟩

end Localization

section Int

/-- Two representations of `G` on finitely generated torsion-free `ℤ`-modules whose
rationalizations `ℚ ⊗[ℤ] V` and `ℚ ⊗[ℤ] W` are equivalent admit an injective intertwining map
`V → W` with finite cokernel. -/
theorem _root_.Representation.Equiv.exists_injective_finite_quotient_range {G : Type*} [Monoid G]
    {V W : Type*} [AddCommGroup V] [Module ℤ V] [Module.Finite ℤ V] [Module.IsTorsionFree ℤ V]
    [AddCommGroup W] [Module ℤ W] [Module.Finite ℤ W] [Module.IsTorsionFree ℤ W]
    {ρ : Representation ℤ G V} {σ : Representation ℤ G W}
    (e : (Representation.baseChange ℚ ρ).Equiv (Representation.baseChange ℚ σ)) :
    ∃ f : ρ.IntertwiningMap σ, Function.Injective f ∧
      Finite (W ⧸ LinearMap.range f.toLinearMap) := by
  obtain ⟨f, f', s, hf'f, hff'⟩ := e.exists_intertwiningMap_comp_eq_smul (nonZeroDivisors ℤ)
    (fun s ↦ .of_ne_zero (nonZeroDivisors.coe_ne_zero s))
    fun s ↦ .of_ne_zero (nonZeroDivisors.coe_ne_zero s)
  refine ⟨f, fun a b hab ↦ IsSMulRegular.of_ne_zero (nonZeroDivisors.coe_ne_zero s)
    (by simpa only [hf'f] using congrArg f' hab), ?_⟩
  -- `Module.finite_of_fg_torsion` is stated for the canonical `ℤ`-module structure
  obtain rfl := Subsingleton.elim ‹Module ℤ W› (AddCommGroup.toIntModule W)
  refine Module.finite_of_fg_torsion _ fun q ↦ ?_
  obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective _ q
  -- `s • w = f (f' w)` lies in the range of `f`.
  refine ⟨s, ?_⟩
  rw [Submonoid.smul_def, ← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, ← hff']
  exact ⟨f' w, rfl⟩

end Int

end TauCeti
