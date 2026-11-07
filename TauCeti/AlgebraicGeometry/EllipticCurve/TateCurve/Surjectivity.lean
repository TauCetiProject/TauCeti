/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Homomorphism
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Galois
import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.KernelStratum
import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.NodalReduction
import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.NodeStratum
import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.NonsingularStratum

/-!
# The Tate uniformisation is an isomorphism

Let `K` be a complete non-archimedean normed field and `q ∈ Kˣ` with `‖q‖ < 1`. This file proves
that the Tate uniformisation `Kˣ / q^ℤ → E_q(K)` is surjective, and bundles it, with its additivity
and injectivity, as a group isomorphism `Additive (Kˣ / q^ℤ) ≃+ E_q(K)`. The same holds over every
complete normed extension `L` of `K`, for the map `Lˣ / q^ℤ → E_q(L)`; the inverse isomorphisms
are compatible with continuous `K`-algebra maps `L → M`, and in particular with every
`K`-automorphism of an algebraic extension `L`.

An affine point `(x, y)` of `E_q(K)` falls into one of three reduction strata according to `‖x‖`,
and each is the image of a set of parameters:

* `‖x‖ > 1`, the kernel of reduction, is the image of `1 + 𝔪`
  (`TauCeti.exists_tateUniformization_eq_some_iff_one_lt_norm`);
* `‖x‖ = 1`, the points with nonsingular reduction other than infinity, is the image of the units
  `u` with `‖1 - u‖ = 1` (`TauCeti.exists_tateUniformization_eq_some_iff_norm_eq_one`);
* `‖x‖ < 1` forces `‖y‖ < 1` (`TauCeti.norm_lt_one_of_equation`), so the point reduces to the
  node, and it is the image of the strict annulus `‖q‖ < ‖u‖ < 1`
  (`TauCeti.exists_tateUniformization_eq_some_iff_norm_lt_one_and_norm_lt_one`).

The point at infinity is the image of the identity class. Neither a discrete value group nor any
restriction on the characteristic is needed.

## Main results

* `TauCeti.tateUniformization_surjective`: the Tate uniformisation is surjective.
* `TauCeti.tateUniformizationEquiv`: the isomorphism `Additive (Kˣ / q^ℤ) ≃+ E_q(K)`.
* `TauCeti.tateUniformizationBaseChange_surjective`, `TauCeti.tateUniformizationBaseChangeEquiv`:
  the same over a complete normed extension `L`.
* `TauCeti.tateUniformizationBaseChangeEquiv_symm_map`: the inverse isomorphisms are compatible
  with continuous `K`-algebra maps of extensions.
* `TauCeti.tateUniformizationBaseChangeEquiv_symm_map_algEquiv`: the inverse isomorphism is
  Galois-equivariant.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, V.3.
* J. Tate, *A review of non-Archimedean elliptic functions*, in *Elliptic curves, modular forms,
  & Fermat's last theorem* (Hong Kong, 1993), International Press (1995), 162–184.
-/

public section

namespace TauCeti

open WeierstrassCurve WeierstrassCurve.Affine

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- **The Tate uniformisation is surjective.** For a complete non-archimedean normed field `K` and
`q ∈ Kˣ` with `‖q‖ < 1`, every point of `E_q(K)` is the image of a class in `Kˣ / q^ℤ`. -/
theorem tateUniformization_surjective (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    Function.Surjective (tateUniformization q hq) := by
  rintro (_ | ⟨x, y, h⟩)
  · exact ⟨1, tateUniformization_one q hq⟩
  rcases lt_trichotomy ‖x‖ 1 with hx | hx | hx
  · -- the point reduces to the node
    have hy : ‖y‖ < 1 :=
      norm_lt_one_of_equation ((norm_tateCurveA₄_le (q : K) hq).trans hq.le)
        ((norm_tateCurveA₆ (q : K) hq).trans_lt hq) hx ((tateCurveAt_equation_iff q hq).mp h.1)
    obtain ⟨u, -, -, hu⟩ :=
      (exists_tateUniformization_eq_some_iff_norm_lt_one_and_norm_lt_one q hq h).mpr ⟨hx, hy⟩
    exact ⟨u, hu⟩
  · obtain ⟨u, -, -, hu⟩ := (exists_tateUniformization_eq_some_iff_norm_eq_one q hq h).mpr hx
    exact ⟨u, hu⟩
  · obtain ⟨u, -, hu⟩ := (exists_tateUniformization_eq_some_iff_one_lt_norm q hq h).mpr hx
    exact ⟨u, hu⟩

/-- **The Tate uniformisation is bijective.** -/
theorem tateUniformization_bijective (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    Function.Bijective (tateUniformization q hq) :=
  ⟨tateUniformization_injective q hq, tateUniformization_surjective q hq⟩

/-- **The Tate uniformisation as a group isomorphism** `Kˣ / q^ℤ ≃ E_q(K)`, written additively on
the source. -/
noncomputable def tateUniformizationEquiv [DecidableEq K] (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    Additive (Kˣ ⧸ Subgroup.zpowers q) ≃+ (tateCurveAt q hq).toAffine.Point :=
  AddEquiv.ofBijective (tateUniformizationHom q hq) ⟨tateUniformizationHom_injective q hq,
    fun P ↦ let ⟨x, hx⟩ := tateUniformization_surjective q hq P
      ⟨.ofMul x, by rwa [tateUniformizationHom_apply, toMul_ofMul]⟩⟩

@[simp]
theorem tateUniformizationEquiv_apply [DecidableEq K] (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    (x : Additive (Kˣ ⧸ Subgroup.zpowers q)) :
    tateUniformizationEquiv q hq x = tateUniformization q hq x.toMul :=
  tateUniformizationHom_apply q hq x

/-! ### The isomorphism over an extension -/

section Extension

variable (L : Type*) [NormedField L] [NormedAlgebra K L] [CompleteSpace L] [IsUltrametricDist L]

/-- **The Tate uniformisation over an extension is surjective.** For a complete normed extension
`L` of `K`, every point of `E_q(L)` is the image of a class in `Lˣ / q^ℤ`. -/
theorem tateUniformizationBaseChange_surjective (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    Function.Surjective (tateUniformizationBaseChange L q hq) := by
  intro P
  obtain ⟨x, hx⟩ := tateUniformization_surjective (Units.map (algebraMap K L : K →* L) q)
    (by simpa using hq) (cast (congrArg (fun W : WeierstrassCurve L ↦ W.toAffine.Point)
      (baseChange_tateCurveAt L q hq)) P)
  exact ⟨x, by rw [tateUniformizationBaseChange_def, hx, cast_cast, cast_eq]⟩

/-- **The Tate uniformisation over an extension is bijective.** -/
theorem tateUniformizationBaseChange_bijective (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    Function.Bijective (tateUniformizationBaseChange L q hq) :=
  ⟨tateUniformizationBaseChange_injective L q hq, tateUniformizationBaseChange_surjective L q hq⟩

variable [DecidableEq L]

/-- **The Tate uniformisation over an extension as a group isomorphism** `Lˣ / q^ℤ ≃ E_q(L)`,
written additively on the source. -/
noncomputable def tateUniformizationBaseChangeEquiv (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    Additive (Lˣ ⧸ Subgroup.zpowers (Units.map (algebraMap K L : K →* L) q)) ≃+
      ((tateCurveAt q hq)⁄L).toAffine.Point :=
  AddEquiv.ofBijective (tateUniformizationBaseChangeHom L q hq)
    ⟨tateUniformizationBaseChangeHom_injective L q hq,
      fun P ↦ let ⟨x, hx⟩ := tateUniformizationBaseChange_surjective L q hq P
        ⟨.ofMul x, by rwa [tateUniformizationBaseChangeHom_apply, toMul_ofMul]⟩⟩

@[simp]
theorem tateUniformizationBaseChangeEquiv_apply (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    (x : Additive (Lˣ ⧸ Subgroup.zpowers (Units.map (algebraMap K L : K →* L) q))) :
    tateUniformizationBaseChangeEquiv L q hq x = tateUniformizationBaseChange L q hq x.toMul :=
  tateUniformizationBaseChangeHom_apply L q hq x

variable {L} {M : Type*} [NormedField M] [NormedAlgebra K M] [CompleteSpace M]
  [IsUltrametricDist M] [DecidableEq M]

/-- **The inverse Tate uniformisation is compatible with continuous maps of extensions**: for a
continuous `K`-algebra map `ι : L → M`, the parameter of the image under `ι` of a point `P` of
`E_q(L)` is the image under `ι` of the parameter of `P`. -/
theorem tateUniformizationBaseChangeEquiv_symm_map (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    (ι : L →ₐ[K] M) (hι : Continuous ι) (P : ((tateCurveAt q hq)⁄L).toAffine.Point) :
    (tateUniformizationBaseChangeEquiv M q hq).symm (Point.map ι P) =
      .ofMul (tateParameterMap q ι ((tateUniformizationBaseChangeEquiv L q hq).symm P).toMul) := by
  rw [AddEquiv.symm_apply_eq, tateUniformizationBaseChangeEquiv_apply, toMul_ofMul,
    ← map_tateUniformizationBaseChange q hq ι hι, ← tateUniformizationBaseChangeEquiv_apply,
    AddEquiv.apply_symm_apply]

/-- **The inverse Tate uniformisation is Galois-equivariant.** For an algebraic extension `L/K`
and a `K`-automorphism `σ` of `L`, the parameter of `σ P` is `σ` applied to the parameter of
`P`. -/
theorem tateUniformizationBaseChangeEquiv_symm_map_algEquiv [Algebra.IsAlgebraic K L] (q : Kˣ)
    (hq : ‖(q : K)‖ < 1) (σ : L ≃ₐ[K] L) (P : ((tateCurveAt q hq)⁄L).toAffine.Point) :
    (tateUniformizationBaseChangeEquiv L q hq).symm (Point.map (σ : L →ₐ[K] L) P) =
      .ofMul (tateParameterMap q (σ : L →ₐ[K] L)
        ((tateUniformizationBaseChangeEquiv L q hq).symm P).toMul) := by
  rw [AddEquiv.symm_apply_eq, tateUniformizationBaseChangeEquiv_apply, toMul_ofMul,
    ← map_algEquiv_tateUniformizationBaseChange q hq σ,
    ← tateUniformizationBaseChangeEquiv_apply, AddEquiv.apply_symm_apply]

end Extension

end TauCeti

end
