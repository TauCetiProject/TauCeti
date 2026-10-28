/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.JordanSplitting.Basic
import TauCeti.LinearAlgebra.BilinearForm.Even.Basic

/-!
# Parity of Jordan constituents

The parity of a Jordan constituent must be measured relative to its own scale: a vector in
a constituent of scale `π ^ j` is even at that scale when its self-pairing lies in
`π ^ (j + 1) R`. In particular, at the dyadic prime a scale-two unary block is odd at its
own scale, although all its self-pairings are divisible by two.

For free constituents, `LinearMap.BilinForm.IsScaleEven` says that the norm ideal lies in `π`
times the constituent's own scale ideal. Zero constituents satisfy this condition, giving the
even convention at an empty scale. For symmetric forms at `π = 2`, this is the usual type II
condition on dyadic Jordan constituents: polarization gives the reverse containment in twice
the scale ideal.

The condition on the `j`-th constituent is equivalent to an intrinsic condition on the form:
every vector pairing into `π ^ j R` has self-pairing in `π ^ (j + 1) R`. It follows that this
condition is independent of the Jordan splitting and is invariant under isometry. The
divisibility statements hold over any commutative ring with a non-zero-divisor `π`. Over a local
ring, a constituent that is even at its own scale has even rank, since its unimodular rescaling
is then a perfect pairing with non-unit diagonal.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, 93:28--29, for invariants of dyadic Jordan
  splittings.
* Sungmun Cho, *Group schemes and local densities of quadratic lattices in residue
  characteristic 2*, [Definition 2.1(b)](https://arxiv.org/pdf/1210.7625#page=3), for parity
  relative to a modular lattice's own scale.
-/

public section

namespace LinearMap.BilinForm

open LinearMap (BilinForm)

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {B : BilinForm R M}
  {π : R} {N : ℕ → Submodule R M}

/-- A constituent has self-pairings divisible by one more power of `π` exactly when every vector
pairing into its scale does. This characterizes its parity without choosing a splitting. -/
theorem IsJordanSplitting.forall_pow_succ_dvd_self_iff (h : B.IsJordanSplitting π N)
    (hπ : π ∈ nonZeroDivisors R) (j : ℕ) :
    (∀ x : N j, π ^ (j + 1) ∣ B x x) ↔
      ∀ x : M, (∀ y, π ^ j ∣ B x y) → π ^ (j + 1) ∣ B x x := by
  constructor
  · intro hself x hx
    obtain ⟨f, _, hf⟩ := h.exists_pow_succ_dvd_sub hπ j
    simpa using (hf x x hx hx).add (hself (f x))
  · intro hself x
    exact hself x (h.pow_dvd_apply x.2)

/-- A free Jordan constituent is even at its own scale `π ^ j` exactly when every one of its
vectors has self-pairing divisible by `π ^ (j + 1)`. -/
theorem IsJordanSplitting.isScaleEven_restrict_iff (h : B.IsJordanSplitting π N) (j : ℕ)
    [Module.Free R (N j)] :
    (B.restrict (N j)).IsScaleEven π ↔ ∀ x ∈ N j, π ^ (j + 1) ∣ B x x := by
  rw [LinearMap.BilinForm.isScaleEven_iff, (h.isModular j).normIdeal_le_mul_scaleIdeal_iff,
    normIdeal_le_iff, ← pow_succ']
  simp [Ideal.mem_span_singleton]

/-- **A constituent that is even at its own scale has even rank.** Over a local ring, if the
constituent `N j` of a Jordan splitting of a symmetric form on a finite free module is even at
its own scale, with `π` a non-unit non-zero-divisor, then its unimodular rescaling is a perfect
pairing whose self-pairings are non-units, so `N j` has even rank. At `π = 2` over `ℤ_2` this
says that a dyadic constituent of type II has even rank. -/
theorem IsJordanSplitting.even_finrank_of_isScaleEven [IsLocalRing R] [Module.Free R M]
    [Module.Finite R M] (h : B.IsJordanSplitting π N) (hB : B.IsSymm)
    (hπ : π ∈ nonZeroDivisors R) (hπ' : ¬IsUnit π) {j : ℕ}
    (he : (B.restrict (N j)).IsScaleEven π) : Even (Module.finrank R (N j)) := by
  have : Module.Free R (N j) := h.free j
  have : Module.Finite R (N j) := h.finite j
  have hpow : π ^ j ∈ nonZeroDivisors R := pow_mem hπ j
  obtain ⟨C, hC, hCp⟩ := isModular_def.mp (h.isModular j)
  have hBC : ∀ x y : N j, B x y = π ^ j * C x y := fun x y ↦ by
    simpa using (LinearMap.congr_fun₂ hC x y).symm
  have hCsymm : C.IsSymm := isSymm_def.mpr fun x y ↦
    (mul_cancel_left_mem_nonZeroDivisors hpow).mp (by rw [← hBC, ← hBC, hB.eq])
  have hdiag : ∀ x, ¬IsUnit (C x x) := fun x hx ↦ by
    obtain ⟨c, hc⟩ := (h.isScaleEven_restrict_iff j).mp he x x.2
    rw [hBC, pow_succ, mul_assoc] at hc
    exact hπ' (isUnit_of_dvd_unit ⟨c, (mul_cancel_left_mem_nonZeroDivisors hpow).mp hc⟩ hx)
  have : C.IsPerfPair := hCp
  exact hCsymm.even_finrank_of_isPerfPair C hdiag

/-- Scale-relative parity is independent of the Jordan splitting. At `π = 2` this is invariance
of dyadic parity type. Zero constituents are scale-even. Freeness is only needed for the two
constituents being compared. -/
theorem IsJordanSplitting.isScaleEven_iff
    {N' : ℕ → Submodule R M} (h : B.IsJordanSplitting π N)
    (h' : B.IsJordanSplitting π N') (hπ : π ∈ nonZeroDivisors R) (j : ℕ)
    [Module.Free R (N j)] [Module.Free R (N' j)] :
    (B.restrict (N j)).IsScaleEven π ↔ (B.restrict (N' j)).IsScaleEven π := by
  rw [h.isScaleEven_restrict_iff j, h'.isScaleEven_restrict_iff j]
  simpa only [Subtype.forall] using
    (h.forall_pow_succ_dvd_self_iff hπ j).trans (h'.forall_pow_succ_dvd_self_iff hπ j).symm

/-- Parity relative to the constituent's own scale is an isometry invariant. In particular,
Jordan splittings of isometric dyadic forms have the same type at every scale. -/
theorem IsJordanSplitting.isScaleEven_iff_of_equivalent
    {M' : Type*} [AddCommGroup M'] [Module R M'] {B' : BilinForm R M'}
    {N' : ℕ → Submodule R M'} (h : B.IsJordanSplitting π N) (h' : B'.IsJordanSplitting π N')
    (hB : B.Equivalent B') (hπ : π ∈ nonZeroDivisors R) (j : ℕ)
    [Module.Free R (N j)] [Module.Free R (N' j)] :
    (B.restrict (N j)).IsScaleEven π ↔ (B'.restrict (N' j)).IsScaleEven π := by
  have hN := h.forall_pow_succ_dvd_self_iff hπ j
  have hN' := h'.forall_pow_succ_dvd_self_iff hπ j
  simp only [Subtype.forall] at hN hN'
  rw [h.isScaleEven_restrict_iff j, h'.isScaleEven_restrict_iff j, hN, hN']
  obtain ⟨e⟩ := hB
  constructor
  · intro H x hx
    obtain ⟨x, rfl⟩ := e.surjective x
    simp only [IsometryEquiv.coe_toLinearEquiv, e.map_app] at hx ⊢
    apply H x
    intro y
    simpa only [e.map_app] using hx (e y)
  · intro H x hx
    rw [← e.map_app]
    apply H (e x)
    intro y
    obtain ⟨y, rfl⟩ := e.surjective y
    simpa only [IsometryEquiv.coe_toLinearEquiv, e.map_app] using hx y

end LinearMap.BilinForm
