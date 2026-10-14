/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.AdmissibleIdeal.Basic
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Truncation

/-!
# Admissibility of presentation kernels

An algebra map from a path algebra has admissible kernel if its arrows land in a nilpotent
two-sided ideal `J` and the images of the vertices and arrows are linearly independent modulo
`J²`. Nilpotence kills all sufficiently long paths. Independence modulo `J²` ensures that a
relation cannot involve paths of length zero or one.

These are the two checks needed for presentations of finite-dimensional basic algebras: take
`J` to be the Jacobson radical and choose arrows lifting a basis of its first radical layer.
The criterion itself needs neither finite-dimensionality nor surjectivity of the map, and
allows infinitely many arrows. In particular it can be used before proving surjectivity.

The argument follows Assem--Simson--Skowroński,
*Elements of the Representation Theory of Associative Algebras I*, Chapter II, §3.
It uses the short-path basis of the quotient by an arrow-ideal power.
-/

public section

namespace AlgHom

open TauCeti TauCeti.PathAlgebra

universe u v w z

variable {k : Type w} {Q : Type u} {A : Type z}
variable [Quiver.{v} Q] [_root_.Finite Q]

section Semiring

variable [CommSemiring k] [Semiring A] [Algebra k A]

/-- If every arrow maps into `J`, the `n`th power of the arrow ideal maps into `J^n`. -/
theorem arrowIdeal_pow_le_comap (f : pathAlgebra k Q →ₐ[k] A) (J : Ideal A)
    (harrows : ∀ (i j : Q) (a : i ⟶ j), f (ofArrow a) ∈ J) (n : ℕ) :
    arrowIdeal k Q ^ n ≤ (J ^ n).comap f := by
  have h₁ : arrowIdeal k Q ≤ J.comap f := by
    rw [arrowIdeal_eq_span_arrows]
    exact Ideal.span_le.mpr (by rintro _ ⟨⟨i, j, a⟩, rfl⟩; exact harrows i j a)
  induction n with
  | zero => simp [Submodule.pow_zero, Ideal.one_eq_top]
  | succ n ih =>
    rw [Submodule.pow_succ, Submodule.pow_succ]
    apply Ideal.mul_le.mpr
    intro x hx y hy
    simpa only [Ideal.mem_comap, map_mul] using
      Ideal.mul_mem_mul (Ideal.mem_comap.mp (ih hx)) (Ideal.mem_comap.mp (h₁ hy))

end Semiring

variable [CommRing k] [Ring A] [Algebra k A]

/-- If arrows map into `J` and vertices and arrows are independent modulo `J²`, the preimage
of `J²` is exactly the square of the arrow ideal. Thus the map identifies the first two path
layers with their images, without requiring surjectivity. -/
theorem comap_sq_eq_arrowIdeal_sq (f : pathAlgebra k Q →ₐ[k] A) (J : Ideal A)
    [J.IsTwoSided]
    (harrows : ∀ (i j : Q) (a : i ⟶ j), f (ofArrow a) ∈ J)
    (hind : LinearIndependent k fun p : ShortPath Q 2 =>
      Ideal.Quotient.mk (J ^ 2) (f (ofPath p.1))) :
    (J ^ 2).comap f = arrowIdeal k Q ^ 2 := by
  have hle := f.arrowIdeal_pow_le_comap J harrows 2
  let g := Ideal.quotientMapₐ (J ^ 2) f hle
  have hg : Function.Injective g := by
    apply g.toLinearMap.injective_of_linearIndependent
      (arrowIdealQuotientBasis k Q 2).span_eq
    simpa only [g, Function.comp_def, AlgHom.toLinearMap_apply,
      arrowIdealQuotientBasis_apply, Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk]
      using hind
  apply le_antisymm _ hle
  intro x hx
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply hg
  simpa only [g, Ideal.quotient_map_mkₐ, map_zero, Ideal.Quotient.mkₐ_eq_mk]
    using Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_comap.mp hx)

/-- A path-algebra map whose arrows lie in a nilpotent two-sided ideal and whose vertices and
arrows are independent modulo its square has admissible kernel. -/
theorem isAdmissibleIdeal_ker (f : pathAlgebra k Q →ₐ[k] A) (J : Ideal A)
    [J.IsTwoSided] (hnil : IsNilpotent J)
    (harrows : ∀ (i j : Q) (a : i ⟶ j), f (ofArrow a) ∈ J)
    (hind : LinearIndependent k fun p : ShortPath Q 2 =>
      Ideal.Quotient.mk (J ^ 2) (f (ofPath p.1))) :
    IsAdmissibleIdeal (RingHom.ker f.toRingHom) where
  exists_arrowIdeal_pow_le := by
    obtain ⟨n, hn⟩ := hnil
    refine ⟨n, ?_⟩
    intro x hx
    have hmem := Ideal.mem_comap.mp (f.arrowIdeal_pow_le_comap J harrows n hx)
    rw [hn] at hmem
    exact RingHom.mem_ker.mpr (Ideal.mem_bot.mp hmem)
  le_arrowIdeal_sq := by
    rw [← f.comap_sq_eq_arrowIdeal_sq J harrows hind]
    exact Ideal.comap_mono bot_le

end AlgHom
