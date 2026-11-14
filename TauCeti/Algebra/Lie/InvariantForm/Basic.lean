/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.TraceForm
public import TauCeti.Algebra.Lie.Dual
import TauCeti.Algebra.Lie.SkewAdjoint

/-!
# Invariant bilinear forms on Lie modules

A bilinear form `Φ` on a Lie module `M` is invariant when `Φ ⁅x, y⁆ z = -Φ y ⁅x, z⁆`
(`LinearMap.BilinForm.lieInvariant`). On a Lie algebra, a symmetric invariant form satisfies the
cyclic identity `Φ ⁅b, c⁆ a = Φ ⁅a, b⁆ c`. This file collects the invariant symmetric forms into the
submodule `TauCeti.LieModule.invariantForms R L M` and shows that on a finite-dimensional
irreducible module over an algebraically closed field there is at most one invariant form up to
scalars.

For a right-separating invariant form on a Lie algebra, the orthogonal complement of its
derived ideal is its centre. This criterion needs no positivity or finite-dimensionality.

On a Lie module, invariance moves the action of `x` from one argument to the other at the cost of
a sign, so an invariant form pairs eigenspaces of `x` only with the opposite eigenspaces. On an
irreducible module the kernels of an invariant form are Lie submodules, so a nonzero invariant
form is nondegenerate.

The irreducible-module uniqueness result follows from Schur's lemma. Invariance of `Φ` says
exactly that `Φ`, read as a linear map
`M → M*`, is a morphism of Lie modules (`LinearMap.BilinForm.lieInvariant_iff` together with
`LieModule.maxTrivLinearMapEquivLieModuleHom`), and the morphism space between the irreducible
modules `M` and `M*` is at most a line (`TauCeti.LieModule.finrank_lieModuleHom_le_one`, with
`TauCeti.LieModule.isIrreducible_dual`). No nondegeneracy or symmetry of the forms is needed.

For the adjoint module of a simple Lie algebra this makes every invariant form a multiple of the
Killing form; that consequence is `TauCeti/Algebra/Lie/Killing/InvariantForm.lean`.

## Main definitions

* `TauCeti.LieModule.invariantForms`: the submodule of invariant symmetric bilinear forms on a Lie
  module.

## Main results

* `LinearMap.BilinForm.orthogonal_derivedSeries_one_eq_center`: for a right-separating invariant
  form, the orthogonal complement of the derived ideal is the centre.
* `LinearMap.BilinForm.lieInvariant.compl₁₂`: pullback along a Lie homomorphism preserves
  invariance.
* `LinearMap.BilinForm.lieInvariant.apply_lie_cyclic`: a symmetric invariant form satisfies
  `Φ ⁅b, c⁆ a = Φ ⁅a, b⁆ c`.
* `LinearMap.BilinForm.lieInvariant.apply_pow_toEnd`: moving `n` copies of the action of `x`
  across an invariant form costs the sign `(-1) ^ n`.
* `LinearMap.BilinForm.lieInvariant.apply_eq_zero_of_mem_eigenspace_of_add_ne_zero`: an invariant
  form pairs the `c`-eigenspace of `x` only with its `-c`-eigenspace.
* `LinearMap.BilinForm.lieInvariant.nondegenerate_of_isIrreducible`: a nonzero invariant form on
  an irreducible module is nondegenerate.
* `LinearMap.BilinForm.lieInvariant.apply_ne_zero_of_eigenspace_neg_le`: on an irreducible
  module, a nonzero invariant form pairs an eigenvector of a diagonalizable element nontrivially
  with any vector spanning the opposite eigenspace.
* `TauCeti.LieModule.traceForm_mem_invariantForms`: the trace form of a Lie module, in particular
  the Killing form, is an invariant symmetric form on the Lie algebra.
* `TauCeti.LieModule.invariantForms_le_maxTrivSubmodule`: invariant symmetric forms lie in the
  maximal trivial submodule of the space of bilinear forms.
* `TauCeti.LieModule.finrank_maxTrivSubmodule_bilinForm_le_one`: the invariant bilinear forms on a
  finite-dimensional irreducible module over an algebraically closed field form a space of
  dimension at most one.
* `TauCeti.LieModule.finrank_invariantForms_le_one`: so do the invariant symmetric forms.
* `TauCeti.LieModule.exists_eq_smul_of_lieInvariant`: on such a module, every invariant form is a
  scalar multiple of any nonzero invariant form.
* `TauCeti.LieModule.invariantForms_eq_span_singleton`: the invariant symmetric forms are the line
  spanned by any nonzero one.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §6.1 for
  Schur's lemma.
* J. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups*, Springer (2012),
  Lemma 12.1.2, for the centre/derived orthogonality criterion.
-/

public section

/-- Pullback along a Lie homomorphism preserves invariance of a bilinear form. -/
theorem LinearMap.BilinForm.lieInvariant.compl₁₂ {R L L' : Type*} [CommRing R]
    [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']
    {B : LinearMap.BilinForm R L} (hB : B.lieInvariant L) (f : L' →ₗ⁅R⁆ L) :
    LinearMap.BilinForm.lieInvariant L' (B.compl₁₂ f.toLinearMap f.toLinearMap) := by
  intro x y z
  simpa only [LinearMap.compl₁₂_apply, LieHom.map_lie, LieHom.coe_toLinearMap] using
    hB (f x) (f y) (f z)

open Module (Dual finrank)

/-! ### The cyclic identity -/

namespace LinearMap.BilinForm.lieInvariant

variable {R L : Type*} [CommRing R] [LieRing L] [Module R L] {Φ : LinearMap.BilinForm R L}

/-- A symmetric invariant form on a Lie algebra is invariant under cyclic permutation of a
bracket and a third argument: `Φ ⁅b, c⁆ a = Φ ⁅a, b⁆ c`. -/
theorem apply_lie_cyclic (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) (a b c : L) :
    Φ ⁅b, c⁆ a = Φ ⁅a, b⁆ c := by
  rw [hΦ, ← lie_skew a b, map_neg, LinearMap.neg_apply, hΦs.eq]

/-! ### Invariant forms on a Lie module -/

section Module

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
  [LieRingModule L M] [_root_.LieModule R L M] {Φ : LinearMap.BilinForm R M}

/-- **Iterated invariance**: moving `n` copies of the action of `x` from one argument of an
invariant form to the other costs the sign `(-1) ^ n`. -/
theorem apply_pow_toEnd (hΦ : Φ.lieInvariant L) (x : L) (n : ℕ) (y z : M) :
    Φ ((LieModule.toEnd R L M x ^ n) y) z = (-1) ^ n * Φ y ((LieModule.toEnd R L M x ^ n) z) := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_apply_eq_comp, ih, LieModule.toEnd_apply_apply, hΦ, ← pow_succ,
      pow_succ' (LieModule.toEnd R L M x) n, mul_apply_eq_comp, LieModule.toEnd_apply_apply]
    ring

/-- **An invariant form pairs eigenspaces only with their opposites.** If `x` acts on `y` and `z`
with eigenvalues `c` and `d` and `c + d ≠ 0`, then `Φ y z = 0`: invariance gives
`(c + d) * Φ y z = 0`. -/
theorem apply_eq_zero_of_mem_eigenspace_of_add_ne_zero [NoZeroDivisors R]
    (hΦ : Φ.lieInvariant L) {x : L} {c d : R} {y z : M}
    (hy : y ∈ (LieModule.toEnd R L M x).eigenspace c)
    (hz : z ∈ (LieModule.toEnd R L M x).eigenspace d) (hcd : c + d ≠ 0) : Φ y z = 0 := by
  have h := hΦ x y z
  rw [← LieModule.toEnd_apply_apply (R := R) (x := x) (m := y),
    ← LieModule.toEnd_apply_apply (R := R) (x := x) (m := z),
    Module.End.mem_eigenspace_iff.mp hy, Module.End.mem_eigenspace_iff.mp hz] at h
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
  exact (mul_eq_zero.mp (by linear_combination h : (c + d) * Φ y z = 0)).resolve_left hcd

omit [LieAlgebra R L] [_root_.LieModule R L M] in
/-- **A nonzero invariant form on an irreducible Lie module is nondegenerate.** Its left kernel
and its right kernel are Lie submodules, by invariance, and neither is everything since the form
is nonzero; irreducibility makes both zero. -/
theorem nondegenerate_of_isIrreducible [_root_.LieModule.IsIrreducible R L M]
    (hΦ : Φ.lieInvariant L) (hΦ0 : Φ ≠ 0) : Φ.Nondegenerate := by
  -- the left kernel of an invariant form is a Lie submodule, hence zero or everything
  have hleft (Ψ : LinearMap.BilinForm R M) (hΨ : Ψ.lieInvariant L) (hΨ0 : Ψ ≠ 0) :
      Ψ.SeparatingLeft := by
    let N := LieAlgebra.InvariantForm.orthogonal (LinearMap.flip Ψ)
      (TauCeti.LieAlgebra.lieInvariant_flip hΨ) ⊤
    have hmem {y : M} : y ∈ N ↔ ∀ z, Ψ y z = 0 := by
      simp [N, LieAlgebra.InvariantForm.mem_orthogonal]
    rcases eq_bot_or_eq_top N with hN | hN
    · intro y hy
      simpa [hN] using hmem.mpr hy
    · exact (hΨ0 (LinearMap.ext fun y ↦ LinearMap.ext fun z ↦
        hmem.mp (hN ▸ LieSubmodule.mem_top y) z)).elim
  refine ⟨hleft Φ hΦ hΦ0, LinearMap.flip_separatingLeft.mp
    (hleft (LinearMap.flip Φ) (TauCeti.LieAlgebra.lieInvariant_flip hΦ) fun h ↦ ?_)⟩
  exact hΦ0 (LinearMap.ext fun y ↦ LinearMap.ext fun z ↦ by
    simpa using LinearMap.congr_fun₂ h z y)

/-- **A nonzero invariant form pairs an eigenvector with its opposite eigenspace.** Let `x` act
diagonalizably on an irreducible module `M` and let `u ≠ 0` be an eigenvector of eigenvalue `c`.
An invariant form pairs the `c`-eigenspace only with the `-c`-eigenspace, so if that eigenspace
lies on the line through `w` and `Φ` is nonzero, then `Φ u w ≠ 0`. -/
theorem apply_ne_zero_of_eigenspace_neg_le [NoZeroDivisors R]
    [_root_.LieModule.IsIrreducible R L M]
    (hΦ : Φ.lieInvariant L) (hΦ0 : Φ ≠ 0) {x : L} {c : R} {u w : M} (hu0 : u ≠ 0)
    (hu : ⁅x, u⁆ = c • u) (htop : ⨆ μ, (LieModule.toEnd R L M x).eigenspace μ = ⊤)
    (hw : (LieModule.toEnd R L M x).eigenspace (-c) ≤ R ∙ w) : Φ u w ≠ 0 := by
  intro huw
  refine hu0 ((hΦ.nondegenerate_of_isIrreducible hΦ0).1 u fun y ↦ ?_)
  have hy : y ∈ ⨆ μ, (LieModule.toEnd R L M x).eigenspace μ := htop ▸ Submodule.mem_top
  induction hy using Submodule.iSup_induction' with
  | mem μ y hy =>
    by_cases hμ : μ = -c
    · subst hμ
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp (hw hy)
      simp [huw]
    · exact hΦ.apply_eq_zero_of_mem_eigenspace_of_add_ne_zero
        (Module.End.mem_eigenspace_iff.mpr hu) hy fun h' ↦ hμ (by linear_combination h')
  | zero => simp
  | add y z _ _ hy hz => simp [hy, hz]

end Module

end LinearMap.BilinForm.lieInvariant

namespace LinearMap.BilinForm

open LieAlgebra

variable {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]

/-- The orthogonal complement of the derived ideal for a right-separating invariant form
is the centre. -/
theorem orthogonal_derivedSeries_one_eq_center (B : LinearMap.BilinForm K L)
    (hB : B.SeparatingRight) (hinv : B.lieInvariant L) :
    LieAlgebra.InvariantForm.orthogonal B hinv (derivedSeries K L 1) = center K L := by
  ext z
  rw [LieAlgebra.InvariantForm.mem_orthogonal, LieModule.mem_maxTrivSubmodule]
  constructor
  · intro hz x
    apply hB
    intro y
    have hxy : ⁅x, y⁆ ∈ derivedSeries K L 1 :=
      LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) (LieSubmodule.mem_top y)
    exact neg_eq_zero.mp ((hinv x y z).symm.trans (hz _ hxy))
  · intro hz d hd
    have hker : (derivedSeries K L 1).toSubmodule ≤ LinearMap.ker (B.flip z) := by
      rw [← LieIdeal.toLieSubalgebra_toSubmodule, coe_derivedSeries_one_eq]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨x, y, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.BilinForm.flip_apply, hinv, hz x,
        map_zero, neg_zero]
    simpa only [LinearMap.mem_ker, LinearMap.BilinForm.flip_apply] using hker hd

end LinearMap.BilinForm

namespace TauCeti.LieModule

/-! ### The submodule of invariant symmetric forms -/

section CommRing

variable (R L M : Type*) [CommRing R] [LieRing L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M]

/-- The invariant symmetric bilinear forms on a Lie module `M`: the forms `Φ` with
`Φ ⁅x, y⁆ z = -Φ y ⁅x, z⁆` and `Φ y z = Φ z y`. -/
def invariantForms : Submodule R (LinearMap.BilinForm R M) where
  carrier := {Φ | Φ.lieInvariant L ∧ Φ.IsSymm}
  zero_mem' := ⟨fun _ _ _ ↦ by simp, LinearMap.BilinForm.isSymm_zero⟩
  add_mem' {Φ Ψ} hΦ hΨ :=
    ⟨fun x y z ↦ by simp only [LinearMap.add_apply, hΦ.1 x y z, hΨ.1 x y z, neg_add],
      hΦ.2.add hΨ.2⟩
  smul_mem' c Φ hΦ := ⟨fun x y z ↦ by simp [hΦ.1 x y z], hΦ.2.smul c⟩

variable {R L M} in
@[simp]
theorem mem_invariantForms_iff {Φ : LinearMap.BilinForm R M} :
    Φ ∈ invariantForms R L M ↔ Φ.lieInvariant L ∧ Φ.IsSymm :=
  Iff.rfl

variable [LieAlgebra R L] [_root_.LieModule R L M]

/-- The trace form of a Lie module `M` is an invariant symmetric form on the Lie algebra `L`. For
`M = L` this is the Killing form `killingForm R L`. -/
theorem traceForm_mem_invariantForms :
    _root_.LieModule.traceForm R L M ∈ invariantForms R L L :=
  ⟨_root_.LieModule.traceForm_lieInvariant R L M,
    LinearMap.BilinForm.isSymm_iff.mpr (_root_.LieModule.traceForm_isSymm R L M)⟩

/-- Invariant symmetric forms lie in the maximal trivial submodule of the space of bilinear forms,
which consists of the invariant forms by `LinearMap.BilinForm.lieInvariant_iff`. -/
theorem invariantForms_le_maxTrivSubmodule :
    invariantForms R L M ≤
      (_root_.LieModule.maxTrivSubmodule R L (LinearMap.BilinForm R M)).toSubmodule :=
  fun Φ hΦ ↦ Φ.lieInvariant_iff.mp hΦ.1

end CommRing

/-! ### Invariant forms on an irreducible module -/

section IsAlgClosed

variable {K L M : Type*} [Field K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L]
variable [AddCommGroup M] [Module K M] [LieRingModule L M] [_root_.LieModule K L M]
variable [FiniteDimensional K M] [_root_.LieModule.IsIrreducible K L M]

variable (K L M) in
/-- **The invariant bilinear forms on a finite-dimensional irreducible Lie module over an
algebraically closed field form a space of dimension at most one.** Here the invariant forms are
described as the maximal trivial submodule of the space of bilinear forms, as in
`LinearMap.BilinForm.lieInvariant_iff`. -/
theorem finrank_maxTrivSubmodule_bilinForm_le_one :
    finrank K (_root_.LieModule.maxTrivSubmodule K L (LinearMap.BilinForm K M)) ≤ 1 := by
  have _i := isIrreducible_dual (K := K) (L := L) (M := M)
  rw [(_root_.LieModule.maxTrivLinearMapEquivLieModuleHom (R := K) (L := L) (M := M)
    (N := Dual K M)).finrank_eq]
  exact finrank_lieModuleHom_le_one K L

/-- **Invariant bilinear forms on a finite-dimensional irreducible Lie module over an algebraically
closed field are proportional**: every invariant form is a scalar multiple of any nonzero one. -/
theorem exists_eq_smul_of_lieInvariant {Φ Ψ : LinearMap.BilinForm K M} (hΦ : Φ.lieInvariant L)
    (hΨ : Ψ.lieInvariant L) (hΨ0 : Ψ ≠ 0) : ∃ c : K, Φ = c • Ψ := by
  let W := _root_.LieModule.maxTrivSubmodule K L (LinearMap.BilinForm K M)
  let Ψ' : W := ⟨Ψ, Ψ.lieInvariant_iff.mp hΨ⟩
  have hΨ' : Ψ' ≠ 0 := fun h ↦ hΨ0 (congrArg Subtype.val h)
  have _i : Nontrivial W := ⟨⟨Ψ', 0, hΨ'⟩⟩
  have hpos : 0 < finrank K W := Module.finrank_pos (R := K) (M := W)
  have hW : finrank K W = 1 := le_antisymm (finrank_maxTrivSubmodule_bilinForm_le_one K L M) hpos
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hW hΨ' ⟨Φ, Φ.lieInvariant_iff.mp hΦ⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

variable (K L M) in
/-- The invariant symmetric bilinear forms on a finite-dimensional irreducible Lie module over an
algebraically closed field form a space of dimension at most one. -/
theorem finrank_invariantForms_le_one : finrank K (invariantForms K L M) ≤ 1 :=
  (Submodule.finrank_mono (R := K) (M := LinearMap.BilinForm K M)
    (invariantForms_le_maxTrivSubmodule K L M)).trans
    (finrank_maxTrivSubmodule_bilinForm_le_one K L M)

/-- On a finite-dimensional irreducible Lie module over an algebraically closed field, the
invariant symmetric bilinear forms are the line spanned by any nonzero one. -/
theorem invariantForms_eq_span_singleton {Ψ : LinearMap.BilinForm K M}
    (hΨ : Ψ ∈ invariantForms K L M) (hΨ0 : Ψ ≠ 0) : invariantForms K L M = K ∙ Ψ := by
  refine le_antisymm (fun Φ hΦ ↦ ?_) ((Submodule.span_singleton_le_iff_mem _ _).mpr hΨ)
  obtain ⟨c, rfl⟩ := exists_eq_smul_of_lieInvariant hΦ.1 hΨ.1 hΨ0
  exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self Ψ)

end IsAlgClosed

end TauCeti.LieModule
