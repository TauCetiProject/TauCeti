/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.Etale.StandardEtale
public import TauCeti.RingTheory.Kaehler.FormallyEtale
public import TauCeti.RingTheory.Node.Basic
public import TauCeti.RingTheory.RingHom.Quotient
public import TauCeti.RingTheory.Spectrum.Prime.Point

/-!
# Étale charts of a node from a split quadratic equation

Let `W` be a smooth `A`-algebra with étale coordinates `p, q`, that is, elements whose
differentials `dp, dq` form a basis of `Ω[W⁄A]`, and let `P` be a prime of `W` on the section
`p = q = 0`. Consider the zero locus in `Spec W` of

`f = a p² + b p q + c q² - h`, with `a, b, c ∈ W` and `h ∈ A`,

where the quadratic form `a p² + b p q + c q²` is nondegenerate at `P` (its discriminant
`b² - 4ac` does not vanish in `κ(P)`) and split at `P` (it is a product of two linear forms over
`κ(P)`). Near a split node, the equation of a nodal curve inside a smooth relative surface takes
this shape once it is normalized to second order; producing that normalization is not done here.
This file shows that, étale locally around `P` and without changing the residue field, the
quadratic form becomes `s t` in new étale coordinates `s, t` vanishing at `P`. Consequently the
zero locus of `f` is étale over the node chart `A[u, v] ⧸ (uv - h)`. No hypothesis relates `h`
to `P`, so `P` need not lie on this zero locus; when `algebraMap A W h ∈ P` it does, and then the
point `P'` above `P` maps into the section `u = v = 0` of the node chart.

The proof is algebraic. Let `ρ` be a root of `X² + bX + ac` with `2ρ + b` and `ρ + b` invertible;
adjoining it to `W` is a standard étale extension `W₁`, and a residue root of `X² + bX + ac` at
`P` lifts it to a point of `W₁` above `P` with the same residue field. Writing `u = ρ + b`, one
has `u² + ac = bu`, hence

`(u p + c q) (a p + u q) = u (a p² + b p q + c q²)`,

so `s = u p + c q` and `t = u⁻¹ (a p + u q)` satisfy `s t = a p² + b p q + c q²`. Their
differentials are `ds = u dp + c dq` and `dt = u⁻¹ a dp + dq` modulo `p` and `q`, with
determinant `(u² - ac) / u = 2ρ + b`, a unit. Inverting the determinant of `ds, dt` in the basis
`dp, dq` makes `ds, dt` a basis, so `A[X, Y] → W'` given by `X ↦ s` and `Y ↦ t` is étale by the
Jacobian criterion `TauCeti.etale_aeval_of_basis`. The node chart is its base change along
`A[X, Y] → A[X, Y] ⧸ (XY - h)` (`TauCeti.NodeAlgebra.etale_lift_of_etale_aeval`).

## Main results

* `TauCeti.exists_etale_mul_eq_quadratic`: after an étale extension preserving the residue field
  at `P`, the quadratic form is a product `s t` of étale coordinates vanishing at `P`.
* `TauCeti.NodeAlgebra.etale_lift_of_etale_aeval`: if `A[X, Y] → T` given by `X ↦ s` and
  `Y ↦ t` is étale, then so is the map `A[u, v] ⧸ (uv - h) → T ⧸ (st - h)` given by `u ↦ s` and
  `v ↦ t`.
* `TauCeti.exists_etale_nodeAlgebra_hom`: étale locally around `P`, the zero locus of
  `a p² + b p q + c q² - h` is étale over the node chart `A[u, v] ⧸ (uv - h)`, by a map sending
  `u, v` to elements `s, t` of the prime `P'` above `P`.

## References

* [Stacks Project, Section 53.20, Tag 0C58](https://stacks.math.columbia.edu/tag/0C58): families
  of nodal curves and their étale local structure.
* [Stacks Project, Example 55.14.1, Tag 0CDC](https://stacks.math.columbia.edu/tag/0CDC): the
  local model `uv = πⁿ` of a node over a discrete valuation ring.
-/

public section

noncomputable section

open KaehlerDifferential MvPolynomial

namespace TauCeti

universe u v

namespace NodeAlgebra

variable {R : Type u} [CommRing R] (a : R)

/-- In `T ⧸ (xy - a)`, the images of `x` and `y` satisfy the nodal equation. -/
theorem quotient_mk_mul_mk {T : Type*} [CommRing T] [Algebra R T] (x y : T) :
    Ideal.Quotient.mk (Ideal.span {x * y - algebraMap R T a}) x * Ideal.Quotient.mk _ y =
      algebraMap R _ a := by
  rw [← Ideal.Quotient.mk_algebraMap, ← map_mul, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact Ideal.subset_span rfl

/-- If `R[X, Y] → T` given by `X ↦ x` and `Y ↦ y` is étale, then so is the map
`R[u, v] ⧸ (uv - a) → T ⧸ (xy - a)` given by `u ↦ x` and `v ↦ y`: it is the base change of the
former along `R[X, Y] → R[X, Y] ⧸ (XY - a)`. -/
theorem etale_lift_of_etale_aeval {T : Type u} [CommRing T] [Algebra R T] (x y : T)
    (H : (aeval (R := R) ![x, y]).toRingHom.Etale) :
    (lift a _ _ (quotient_mk_mul_mk a x y)).toRingHom.Etale := by
  let I : Ideal (MvPolynomial (Fin 2) R) := RingHom.ker (mk a)
  have hI : I.map (aeval (R := R) ![x, y]) = Ideal.span {x * y - algebraMap R T a} := by
    rw [show I = Ideal.span {X 0 * X 1 - C a} from ker_mk a, Ideal.map_span,
      Set.image_singleton]
    simp
  let e₀ := Ideal.quotientKerAlgEquivOfSurjective (mk_surjective a)
  have heq : lift a _ _ (quotient_mk_mul_mk a x y) =
      ((Ideal.quotientEquivAlgOfEq R hI).toAlgHom.comp
        (Ideal.quotientMapₐ _ (aeval (R := R) ![x, y]) Ideal.le_comap_map)).comp
        e₀.symm.toAlgHom := by
    ext <;> simp [e₀, I, ← mk_X]
  rw [heq]
  exact RingHom.Etale.respectsIso.2 _ e₀.symm.toRingEquiv <|
    RingHom.Etale.respectsIso.1 _ (Ideal.quotientEquivAlgOfEq R hI).toRingEquiv <|
      RingHom.Etale.isStableUnderBaseChange.quotientMap RingHom.Etale.respectsIso _ I H

end NodeAlgebra

/-- The standard étale pair adjoining a root `ρ` of `X² + bX + e` and inverting `2ρ + b` and
`ρ + b`. -/
private def splittingPair {W : Type*} [CommRing W] (b e : W) : StandardEtalePair W where
  f := Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C e
  monic_f := by monicity!
  g := Polynomial.derivative (Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C e) *
    (Polynomial.X + Polynomial.C b)
  cond := ⟨Polynomial.X + Polynomial.C b, 0, 1, by ring⟩

/-- A point of `splittingPair b e` is a root `x` of `X² + bX + e` at which `2x + b` and `x + b`
are units. -/
private theorem splittingPair_hasMap_iff {W : Type*} [CommRing W] (b e : W) {T : Type*}
    [CommRing T] [Algebra W T] (x : T) :
    (splittingPair b e).HasMap x ↔ x ^ 2 + algebraMap W T b * x + algebraMap W T e = 0 ∧
      IsUnit (2 * x + algebraMap W T b) ∧ IsUnit (x + algebraMap W T b) := by
  simp [StandardEtalePair.HasMap, splittingPair, Polynomial.aeval_def, Polynomial.eval₂_mul,
    IsUnit.mul_iff, one_add_one_eq_two, map_ofNat]

/-- If `X² + bX + e` has a root over a field and its discriminant is nonzero, then it has a root
`r` with `2r + b ≠ 0` and `r + b ≠ 0`: if `r + b = 0` then `e = 0`, and the other root `0` works. -/
private theorem exists_root_add_ne_zero {K : Type*} [Field K] {b e : K}
    (hdisc : discrim 1 b e ≠ 0) (hroot : ∃ r : K, r ^ 2 + b * r + e = 0) :
    ∃ r : K, r ^ 2 + b * r + e = 0 ∧ 2 * r + b ≠ 0 ∧ r + b ≠ 0 := by
  have h₂ (r : K) (hr : r ^ 2 + b * r + e = 0) : 2 * r + b ≠ 0 := fun h ↦ hdisc <| by
    rw [discrim_eq_sq_of_quadratic_eq_zero (x := r) (by linear_combination hr), mul_one, h,
      zero_pow two_ne_zero]
  obtain ⟨r, hr⟩ := hroot
  by_cases hrb : r + b = 0
  · have h0 : (0 : K) ^ 2 + b * 0 + e = 0 := by linear_combination hr - r * hrb
    exact ⟨0, h0, h₂ 0 h0, by simpa using h₂ 0 h0⟩
  · exact ⟨r, hr, h₂ r hr, hrb⟩

/-- A residue root of `X² + bX + e` with nonzero discriminant gives a point of `splittingPair b e`
with values in `K`, sending the adjoined root to a root `r` with `2r + b ≠ 0`. -/
private theorem exists_lift_splittingPair {W K : Type*} [CommRing W] [Field K] [Algebra W K]
    {b e : W} (hdisc : discrim 1 (algebraMap W K b) (algebraMap W K e) ≠ 0)
    (hroot : ∃ r : K, r ^ 2 + algebraMap W K b * r + algebraMap W K e = 0) :
    ∃ (r : K) (ψ : (splittingPair b e).Ring →ₐ[W] K), ψ (splittingPair b e).X = r ∧
      r ^ 2 + algebraMap W K b * r + algebraMap W K e = 0 ∧ 2 * r + algebraMap W K b ≠ 0 := by
  obtain ⟨r, hr, hr₂, hr₁⟩ := exists_root_add_ne_zero hdisc hroot
  exact ⟨r, (splittingPair b e).lift r
    ((splittingPair_hasMap_iff b e r).mpr ⟨hr, hr₂.isUnit, hr₁.isUnit⟩),
    (splittingPair b e).lift_X _ _, hr, hr₂⟩

/-- If `ρ` is a root of `X² + bX + ac` and `v` is an inverse of `u = ρ + b`, then
`a p² + b p q + c q² = (u p + c q) (v (a p + u q))`. -/
private theorem mul_eq_quadratic_of_root {W : Type*} [CommRing W] {a b c ρ v : W}
    (hρ : ρ ^ 2 + b * ρ + a * c = 0) (huv : (ρ + b) * v = 1) (p q : W) :
    ((ρ + b) * p + c * q) * (v * (a * p + (ρ + b) * q)) = a * p ^ 2 + b * p * q + c * q ^ 2 := by
  linear_combination (v * p * q) * hρ + (a * p ^ 2 + b * p * q + c * q ^ 2) * huv

/-- Modulo `p` and `q`, the determinant of `d(u p + c q), d(v (a p + u q))` in a basis `dp, dq`
of `Ω[S⁄A]` is `u (v u) - v a c`. -/
private theorem det_D_eq {A S K : Type*} [CommRing A] [CommRing S] [Algebra A S] [CommRing K]
    (B : Module.Basis (Fin 2) S Ω[S⁄A]) {p q : S} (hB₀ : D A S p = B 0) (hB₁ : D A S q = B 1)
    (ψ : S →+* K) (hp : ψ p = 0) (hq : ψ q = 0) (u v a c : S) :
    ψ (B.det ![D A S (u * p + c * q), D A S (v * (a * p + u * q))]) =
      ψ u * (ψ v * ψ u) - ψ v * ψ a * ψ c := by
  simp [Module.Basis.det_apply, Matrix.det_fin_two, Module.Basis.toMatrix_apply, hB₀, hB₁, hp, hq]

section

variable {A : Type u} {W : Type v} [CommRing A] [CommRing W] [Algebra A W]

/-- **A split nondegenerate binary quadratic form in étale coordinates is étale locally a product
of étale coordinates.** Let `W` be a smooth `A`-algebra and `p, q ∈ W` elements whose
differentials form a basis of `Ω[W⁄A]`, both lying in a prime `P`. Let `a, b, c ∈ W` be such that
the discriminant `discrim a b c = b² - 4ac` does not vanish at `P` and `X² + bX + ac` has a root
in `κ(P)`; that is, the quadratic form `a X² + b XY + c Y²` is nondegenerate and splits into
linear factors over `κ(P)`. Then there are an étale `W`-algebra `W'`, a prime `P'` of `W'` above
`P` with the same residue field, and `s, t ∈ P'` with `s t = a p² + b p q + c q²`, such that
`A[X, Y] → W'` given by `X ↦ s` and `Y ↦ t` is étale. -/
theorem exists_etale_mul_eq_quadratic [Algebra.Smooth A W] {p q : W}
    (bW : Module.Basis (Fin 2) W Ω[W⁄A]) (hbW₀ : bW 0 = D A W p) (hbW₁ : bW 1 = D A W q)
    (a b c : W) (P : Ideal W) [P.IsPrime] (hp : p ∈ P) (hq : q ∈ P)
    (hdisc : algebraMap W P.ResidueField (discrim a b c) ≠ 0)
    (hsplit : ∃ r : P.ResidueField,
      r ^ 2 + algebraMap W _ b * r + algebraMap W _ (a * c) = 0) :
    ∃ (W' : Type v) (_ : CommRing W') (_ : Algebra W W') (_ : Algebra.Etale W W')
      (_ : Algebra A W') (_ : IsScalarTower A W W') (P' : Ideal W') (_ : P'.IsPrime)
      (hP' : P = P'.comap (algebraMap W W')) (s t : W'),
      Function.Bijective (Ideal.ResidueField.map P P' (algebraMap W W') hP') ∧
      s ∈ P' ∧ t ∈ P' ∧ s * t = algebraMap W W' (a * p ^ 2 + b * p * q + c * q ^ 2) ∧
      (aeval (R := A) ![s, t]).toRingHom.Etale := by
  set κ := P.ResidueField
  -- Adjoin a root `ρ` of `X² + bX + ac` lifting a residue root `r`, inverting `2ρ + b`, `ρ + b`.
  have hd : discrim 1 (algebraMap W κ b) (algebraMap W κ (a * c)) =
      algebraMap W κ (discrim a b c) := by
    simp only [discrim, map_sub, map_mul, map_pow, map_ofNat]
    ring
  obtain ⟨r, ψ₁, hψ₁ρ, hr, hr₂⟩ := exists_lift_splittingPair (hd ▸ hdisc) hsplit
  let E := splittingPair b (a * c)
  let W₁ := E.Ring
  let : Algebra A W₁ := Algebra.compHom W₁ (algebraMap A W)
  have : IsScalarTower A W W₁ := .of_algebraMap_eq fun _ ↦ rfl
  let ρ : W₁ := E.X
  obtain ⟨hρ, -, hρ₁⟩ := (splittingPair_hasMap_iff b (a * c) ρ).mp E.hasMap_X
  have hψ₁ (w : W) : ψ₁ (algebraMap W W₁ w) = algebraMap W κ w := ψ₁.commutes w
  have hφp : algebraMap W κ p = 0 := Ideal.algebraMap_residueField_eq_zero.mpr hp
  have hφq : algebraMap W κ q = 0 := Ideal.algebraMap_residueField_eq_zero.mpr hq
  -- The factorisation `a p² + b p q + c q² = s₁ t₁` in `W₁`, with `u = ρ + b` and `v = u⁻¹`.
  set u : W₁ := ρ + algebraMap W W₁ b with hu
  let v : W₁ := ↑hρ₁.unit⁻¹
  have huv : u * v = 1 := hρ₁.mul_val_inv
  let s₁ : W₁ := u * algebraMap W W₁ p + algebraMap W W₁ c * algebraMap W W₁ q
  let t₁ : W₁ := v * (algebraMap W W₁ a * algebraMap W W₁ p + u * algebraMap W W₁ q)
  have hst₁ : s₁ * t₁ = algebraMap W W₁ (a * p ^ 2 + b * p * q + c * q ^ 2) := by
    rw [map_mul] at hρ
    simpa using mul_eq_quadratic_of_root hρ huv (algebraMap W W₁ p) (algebraMap W W₁ q)
  -- The determinant `d` of `ds₁, dt₁` in the basis `dp, dq` is `2r + b ≠ 0` at the point `ψ₁`.
  let bW₁ := kaehlerBasisOfFormallyEtale A W W₁ bW
  have hb₀ : D A W₁ (algebraMap W W₁ p) = bW₁ 0 := by simp [bW₁, hbW₀]
  have hb₁ : D A W₁ (algebraMap W W₁ q) = bW₁ 1 := by simp [bW₁, hbW₁]
  let d : W₁ := bW₁.det ![D A W₁ s₁, D A W₁ t₁]
  have hψd : ψ₁ d ≠ 0 := by
    have hU : ψ₁ u = r + algebraMap W κ b := by rw [hu, map_add, hψ₁ρ, hψ₁]
    have hwU : ψ₁ v * ψ₁ u = 1 := by rw [← map_mul, mul_comm v u, huv, map_one]
    have hdet := det_D_eq bW₁ hb₀ hb₁ (ψ₁ : W₁ →+* κ) (by simp [hψ₁, hφp]) (by simp [hψ₁, hφq])
      u v (algebraMap W W₁ a) (algebraMap W W₁ c)
    simp only [RingHom.coe_coe, hψ₁] at hdet
    rw [map_mul] at hr
    have : ψ₁ d = 2 * r + algebraMap W κ b := by
      rw [hdet]
      linear_combination (ψ₁ u + r) * hwU + (1 - ψ₁ v * r) * hU - ψ₁ v * hr
    rw [this]
    exact hr₂
  -- Invert `d`, and take the point `P'` of `W' = W₁[1/d]` given by `ρ ↦ r`.
  let W' := Localization.Away d
  let ψ : W' →ₐ[W] κ := IsLocalization.Away.liftAlgHom d (f := ψ₁) hψd.isUnit
  have hψ (w : W₁) : ψ (algebraMap W₁ W' w) = ψ₁ w :=
    IsLocalization.Away.lift_eq d (g := ψ₁.toRingHom) hψd.isUnit w
  let P' := RingHom.ker ψ
  let s := algebraMap W₁ W' s₁
  let t := algebraMap W₁ W' t₁
  refine ⟨W', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, P',
    RingHom.ker_isPrime _, ψ.comap_ker_eq_of_residueField.symm, s, t,
    ψ.residueFieldMap_bijective, ?_, ?_, ?_, ?_⟩
  · rw [RingHom.mem_ker, hψ]
    simp [s₁, hψ₁, hφp, hφq]
  · rw [RingHom.mem_ker, hψ]
    simp [t₁, hψ₁, hφp, hφq]
  · simp only [s, t, ← map_mul, hst₁, ← IsScalarTower.algebraMap_apply]
  -- `ds, dt` is a basis of `Ω[W'⁄A]`: its determinant in the basis `dp, dq` is the unit `d`.
  let bW' := kaehlerBasisOfFormallyEtale A W₁ W' bW₁
  have hdet : bW'.det ![D A W' s, D A W' t] = algebraMap W₁ W' d := by
    rw [← kaehlerBasisOfFormallyEtale_det_map]
    congr 1
    ext i
    fin_cases i <;> simp [s, t]
  obtain ⟨hli, hspan⟩ := bW'.is_basis_iff_det.mpr
    (hdet ▸ IsLocalization.Away.algebraMap_isUnit d)
  have : Algebra.Smooth A W₁ := .comp A W W₁
  have : Algebra.Smooth A W' := .comp A W₁ W'
  exact etale_aeval_of_basis ![s, t] (.mk hli hspan.ge) fun i ↦ by fin_cases i <;> simp

end

/-- **Étale charts of a node from a split quadratic equation.** Let `W` be a smooth `A`-algebra
and `p, q ∈ W` elements whose differentials form a basis of `Ω[W⁄A]`, both lying in a prime `P`.
Let `a, b, c ∈ W` be such that the quadratic form `a X² + b XY + c Y²` is nondegenerate and split
at `P`, as in `TauCeti.exists_etale_mul_eq_quadratic`, and let `h ∈ A`. Then, after an étale
extension `W → W'` and at a prime `P'` above `P` with the same residue field, the zero locus of
`f = a p² + b p q + c q² - h` admits an étale map to the node chart `A[u, v] ⧸ (uv - h)`: there
are `s, t ∈ P'` and an étale `A`-algebra map `A[u, v] ⧸ (uv - h) → W' ⧸ (f)` sending `u ↦ s` and
`v ↦ t`. -/
theorem exists_etale_nodeAlgebra_hom {A W : Type u} [CommRing A] [CommRing W] [Algebra A W]
    [Algebra.Smooth A W] {p q : W} (bW : Module.Basis (Fin 2) W Ω[W⁄A])
    (hbW₀ : bW 0 = D A W p) (hbW₁ : bW 1 = D A W q) (a b c : W) (h : A) (P : Ideal W)
    [P.IsPrime] (hp : p ∈ P) (hq : q ∈ P)
    (hdisc : algebraMap W P.ResidueField (discrim a b c) ≠ 0)
    (hsplit : ∃ r : P.ResidueField,
      r ^ 2 + algebraMap W _ b * r + algebraMap W _ (a * c) = 0) :
    ∃ (W' : Type u) (_ : CommRing W') (_ : Algebra W W') (_ : Algebra.Etale W W')
      (_ : Algebra A W') (_ : IsScalarTower A W W') (P' : Ideal W') (_ : P'.IsPrime)
      (hP' : P = P'.comap (algebraMap W W')) (s t : W')
      (φ : NodeAlgebra A h →ₐ[A]
        W' ⧸ Ideal.span {algebraMap W W' (a * p ^ 2 + b * p * q + c * q ^ 2 - algebraMap A W h)}),
      Function.Bijective (Ideal.ResidueField.map P P' (algebraMap W W') hP') ∧
      s ∈ P' ∧ t ∈ P' ∧ φ (NodeAlgebra.coord h 0) = Ideal.Quotient.mk _ s ∧
      φ (NodeAlgebra.coord h 1) = Ideal.Quotient.mk _ t ∧ φ.toRingHom.Etale := by
  obtain ⟨W', _, _, _, _, _, P', _, hP', s, t, hκ, hs, ht, hst, H⟩ :=
    exists_etale_mul_eq_quadratic bW hbW₀ hbW₁ a b c P hp hq hdisc hsplit
  have hI : Ideal.span {s * t - algebraMap A W' h} =
      Ideal.span {algebraMap W W' (a * p ^ 2 + b * p * q + c * q ^ 2 - algebraMap A W h)} := by
    rw [map_sub, ← hst, ← IsScalarTower.algebraMap_apply]
  let e := Ideal.quotientEquivAlgOfEq A hI
  refine ⟨W', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, P',
    inferInstance, hP', s, t, e.toAlgHom.comp (NodeAlgebra.lift h _ _
      (NodeAlgebra.quotient_mk_mul_mk h s t)), hκ, hs, ht, ?_, ?_, ?_⟩
  · simp [e]
  · simp [e]
  · exact RingHom.Etale.respectsIso.1 _ e.toRingEquiv
      (NodeAlgebra.etale_lift_of_etale_aeval h s t H)

end TauCeti
