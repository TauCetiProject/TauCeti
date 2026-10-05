/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Exponent
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Descent of linear characters

A linear character of a monoid of exponent dividing `n` takes values in the `n`-th roots of unity.
If a field `K` contains a primitive `n`-th root, every linear character over an extension `L / K`
therefore comes from a unique linear character over `K`. This supplies the coefficient descent
used to realize monomial representations over cyclotomic fields.

The result requires neither characteristic zero nor finiteness of the monoid: a nonzero exponent
bound and a primitive root suffice.

## References

* J.-P. Serre, *Linear Representations of Finite Groups* (1977), Section 12.3.
-/

public section

universe u v w

namespace TauCeti

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable {G : Type w} [Monoid G]

/-- A linear character descends uniquely along a field extension if its values lie in the image
of the units of the base field. -/
theorem _root_.MonoidHom.existsUnique_unitsMap_comp_eq (χ : G →* Lˣ)
    (hχ : ∀ g, χ g ∈ (Units.map (algebraMap K L : K →* L)).range) :
    ∃! ψ : G →* Kˣ, (Units.map (algebraMap K L : K →* L)).comp ψ = χ := by
  let f := Units.map (algebraMap K L : K →* L)
  have hf : Function.Injective f := Units.map_injective (algebraMap K L).injective
  let e := MonoidHom.ofInjective hf
  let ψ := e.symm.toMonoidHom.comp (χ.codRestrict f.range hχ)
  have hψ : f.comp ψ = χ := by
    apply MonoidHom.ext
    intro g
    exact MonoidHom.apply_ofInjective_symm hf ⟨χ g, hχ g⟩
  refine ⟨ψ, hψ, fun ψ' hψ' => ?_⟩
  apply MonoidHom.ext
  intro g
  apply hf
  exact (DFunLike.congr_fun hψ' g).trans (DFunLike.congr_fun hψ g).symm

/-- A primitive `n`-th root in the base field descends every linear character of a monoid whose
exponent divides the nonzero integer `n`. -/
theorem _root_.MonoidHom.existsUnique_unitsMap_comp_eq_of_isPrimitiveRoot (χ : G →* Lˣ)
    {n : ℕ} [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n) (hG : Monoid.exponent G ∣ n) :
    ∃! ψ : G →* Kˣ, (Units.map (algebraMap K L : K →* L)).comp ψ = χ := by
  apply χ.existsUnique_unitsMap_comp_eq
  intro g
  have hpow : (χ g : L) ^ n = 1 := by
    have hg := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hG g
    simpa only [map_pow, map_one, Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg (fun x : G => (χ x : L)) hg
  obtain ⟨i, -, hi⟩ :=
    (hζ.map_of_injective (algebraMap K L).injective).eq_pow_of_pow_eq_one hpow
  refine ⟨(hζ.isUnit (NeZero.ne n)).unit ^ i, ?_⟩
  apply Units.ext
  simpa using hi

end TauCeti
