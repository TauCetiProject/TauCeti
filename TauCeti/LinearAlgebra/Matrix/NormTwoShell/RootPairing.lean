/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
public import TauCeti.LinearAlgebra.Matrix.NormTwoShell.Basic
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Irreducible

/-!
# The root system of the norm-two shell

Let `B` be a positive definite integer matrix indexed by a finite type `I`, read as the Gram
matrix of the lattice `I → ℤ` with the pairing `⟪a, b⟫ = a ⬝ᵥ B *ᵥ b`. Its norm-two shell
`Φ = {a | ⟪a, a⟫ = 2}` (`Matrix.normTwoShell`) is a finite set, stable under the reflections
`x ↦ x - ⟪x, a⟫ a` in its own vectors. This file makes it a root pairing: over a field `k` of
characteristic zero, the vectors of `Φ` are the roots in `I → k`, the vector `B *ᵥ a` is the coroot
of the root `a`, and the pairing of `M = N = I → k` is the dot product, so that the Cartan integer
of two roots is their lattice pairing `⟪a, b⟫`.

The root pairing is indexed by `Φ` itself, so by construction its roots are exactly the integral
vectors of norm two. It is crystallographic and reduced. When the diagonal entries of `B` are `2`
the coordinate vectors are roots, and it is a root system spanning `I → k`. When moreover the
off-diagonal entries of `B` are nonpositive, as for the Cartan matrix of a simply laced Dynkin
diagram or the symmetrized Cartan matrix `2I - (A + Aᵀ)` of a quiver with positive definite Tits
form, the coordinate vectors form a base whose Cartan matrix is `B` itself, and the root system is
irreducible when the diagram of `B` is connected.

## Main definitions

* `Matrix.PosDef.normTwoShellRootPairing`: the root pairing on the norm-two shell.
* `Matrix.normTwoShellSimple`: the coordinate vector `Pi.single i 1` as a vector of the shell.
* `Matrix.PosDef.normTwoShellBase`: the base of coordinate vectors, for nonpositive off-diagonal
  entries.
* `Matrix.PosDef.normTwoShellBaseEquiv`: the vertices `I` index the simple roots of this base.

## Main results

* `Matrix.PosDef.pairingIn_normTwoShellRootPairing`: the Cartan integer of two roots is their
  lattice pairing.
* `Matrix.PosDef.isRootSystem_normTwoShellRootPairing`: for diagonal `2`, the roots and coroots
  span.
* `Matrix.PosDef.normTwoShellBase_cartanMatrix`: the Cartan matrix of the base is `B`.
* `Matrix.PosDef.isIrreducible_normTwoShellRootPairing`: the root system is irreducible when the
  diagram of `B` is connected.

## References

* I. N. Bernstein, I. M. Gelfand and V. A. Ponomarev, *Coxeter functors and Gabriel's theorem*,
  Russian Math. Surveys 28 (1973), §2, where the roots of a positive definite integral quadratic
  form are made a root system in this way.
* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, Proposition 5.10.
-/

public noncomputable section

open Function Set Module Submodule

namespace Matrix

section Cast

variable {I : Type*} (k : Type*) [Ring k]

/-- The integer vector `a`, read in `I → k`. -/
private def castVec : (I → ℤ) →+ (I → k) := (Int.castAddHom k).compLeft I

private theorem castVec_apply (a : I → ℤ) : castVec k a = fun i ↦ (a i : k) := (rfl)

private theorem castVec_injective [CharZero k] : Injective (castVec (I := I) k) := fun _ _ h ↦
  funext fun i ↦ Int.cast_injective (congrFun h i)

private theorem castVec_dotProduct [Fintype I] {k : Type*} [CommRing k] (a b : I → ℤ) :
    castVec k a ⬝ᵥ castVec k b = ((a ⬝ᵥ b : ℤ) : k) := by
  simp [castVec_apply, dotProduct]

private theorem castVec_eq_sum [Fintype I] [DecidableEq I] (a : I → ℤ) :
    castVec k a = ∑ i, a i • castVec k (Pi.single i 1) := by
  ext j
  simp [castVec_apply, Finset.sum_apply, Pi.single_apply, zsmul_eq_mul]

end Cast

section Simple

variable {I : Type*} [Fintype I] [DecidableEq I] {B : Matrix I I ℤ} (hdiag : ∀ i, B i i = 2)

/-- The coordinate vector `Pi.single i 1`, a vector of the norm-two shell as the diagonal entries
are `2`. -/
def normTwoShellSimple (i : I) : B.normTwoShell :=
  ⟨Pi.single i 1, single_mem_normTwoShell (hdiag i)⟩

@[simp]
theorem coe_normTwoShellSimple (i : I) : (normTwoShellSimple hdiag i : I → ℤ) = Pi.single i 1 :=
  (rfl)

theorem normTwoShellSimple_injective : Injective (normTwoShellSimple (B := B) hdiag) :=
  fun i j h ↦ by
    have := congrFun (congrArg Subtype.val h) i
    by_contra hij
    simp [hij] at this

end Simple

namespace PosDef

variable {I : Type*} [Fintype I] {B : Matrix I I ℤ}

variable (hB : B.PosDef) (k : Type*) [Field k] [CharZero k]

/-- The roots of the norm-two shell, as vectors of `I → k`. -/
private def shellRoot : B.normTwoShell ↪ (I → k) :=
  ⟨fun a ↦ castVec k a.1, fun _ _ h ↦ Subtype.ext (castVec_injective k h)⟩

private theorem shellRoot_apply (a : B.normTwoShell) : shellRoot k a = castVec k a.1 := (rfl)

include hB in
/-- The coroots of the norm-two shell, the vectors `B *ᵥ a` of `I → k`; they are distinct because
`B` is nondegenerate. -/
private def shellCoroot : B.normTwoShell ↪ (I → k) :=
  ⟨fun a ↦ castVec k (B *ᵥ a.1), fun a b h ↦ Subtype.ext <| sub_eq_zero.mp <| by
    by_contra hne
    have hpos := hB.dotProduct_mulVec_pos hne
    have hab : B *ᵥ a.1 = B *ᵥ b.1 := castVec_injective k h
    rw [star_trivial, mulVec_sub, hab, sub_self, dotProduct_zero] at hpos
    exact lt_irrefl 0 hpos⟩

private theorem shellCoroot_apply (a : B.normTwoShell) :
    shellCoroot hB k a = castVec k (B *ᵥ a.1) := (rfl)

variable [DecidableEq I] (hdiag : ∀ i, B i i = 2)

/-- **The root pairing of the norm-two shell.** For a positive definite integer matrix `B`, the
vectors `a` with `a ⬝ᵥ B *ᵥ a = 2`, read in `I → k`, are the roots, and the vector `B *ᵥ a` is the
coroot of the root `a`, for the dot product pairing of `I → k` with itself. Reflection in a root
`a` is `x ↦ x - ⟪x, a⟫ a`, which preserves the lattice form and hence the shell. -/
def normTwoShellRootPairing : RootPairing B.normTwoShell k (I → k) (I → k) :=
  haveI := hB.finite_normTwoShell.to_subtype
  RootPairing.mk' (dotProductEquiv k I).toLinearMap (shellRoot k) (shellCoroot hB k)
    (fun a ↦ by
      rw [LinearEquiv.coe_coe, dotProductEquiv_apply_apply, shellRoot_apply, shellCoroot_apply,
        castVec_dotProduct, mem_normTwoShell.mp a.2, Int.cast_ofNat])
    (by
      rintro a - ⟨b, rfl⟩
      refine ⟨⟨_, hB.isHermitian.isSymm.sub_smul_mem_normTwoShell a.2 b.2⟩, ?_⟩
      rw [shellRoot_apply, preReflection_apply, LinearMap.flip_apply, LinearEquiv.coe_coe,
        dotProductEquiv_apply_apply, shellRoot_apply, shellRoot_apply, shellCoroot_apply,
        castVec_dotProduct, map_sub, map_zsmul, Int.cast_smul_eq_zsmul])
    (by
      rintro a - ⟨b, rfl⟩
      refine ⟨⟨_, hB.isHermitian.isSymm.sub_smul_mem_normTwoShell a.2 b.2⟩, ?_⟩
      rw [shellCoroot_apply, preReflection_apply, LinearEquiv.coe_coe,
        dotProductEquiv_apply_apply, shellRoot_apply, shellCoroot_apply, shellCoroot_apply,
        castVec_dotProduct, mulVec_sub, mulVec_smul, map_sub, map_zsmul, Int.cast_smul_eq_zsmul,
        hB.isHermitian.isSymm.dotProduct_mulVec_comm (x := b.1) (y := a.1)])

@[simp]
theorem normTwoShellRootPairing_root (a : B.normTwoShell) :
    (hB.normTwoShellRootPairing k).root a = fun i ↦ (a.1 i : k) :=
  (rfl)

@[simp]
theorem normTwoShellRootPairing_coroot (a : B.normTwoShell) :
    (hB.normTwoShellRootPairing k).coroot a = fun i ↦ ((B *ᵥ a.1) i : k) :=
  (rfl)

@[simp]
theorem normTwoShellRootPairing_toLinearMap_apply (x y : I → k) :
    (hB.normTwoShellRootPairing k).toLinearMap x y = x ⬝ᵥ y :=
  (rfl)

/-- The pairing of two roots of the norm-two shell is their lattice pairing. -/
theorem pairing_normTwoShellRootPairing (a b : B.normTwoShell) :
    (hB.normTwoShellRootPairing k).pairing a b = ((a.1 ⬝ᵥ B *ᵥ b.1 : ℤ) : k) := by
  rw [RootPairing.pairing, normTwoShellRootPairing_toLinearMap_apply,
    normTwoShellRootPairing_root, normTwoShellRootPairing_coroot]
  exact castVec_dotProduct _ _

instance : (hB.normTwoShellRootPairing k).IsCrystallographic where
  exists_value a b := ⟨a.1 ⬝ᵥ B *ᵥ b.1, by
    rw [pairing_normTwoShellRootPairing, algebraMap_int_eq, eq_intCast]⟩

/-- **The Cartan integer of two roots of the norm-two shell is their lattice pairing.** -/
@[simp]
theorem pairingIn_normTwoShellRootPairing (a b : B.normTwoShell) :
    (hB.normTwoShellRootPairing k).pairingIn ℤ a b = a.1 ⬝ᵥ B *ᵥ b.1 := by
  apply FaithfulSMul.algebraMap_injective ℤ k
  rw [RootPairing.algebraMap_pairingIn, pairing_normTwoShellRootPairing, algebraMap_int_eq,
    eq_intCast]

include hdiag in
/-- The roots of the norm-two shell span `I → k` once the diagonal entries are `2`, since the
coordinate vectors are then roots; so do the coroots. -/
theorem isRootSystem_normTwoShellRootPairing : (hB.normTwoShellRootPairing k).IsRootSystem := by
  have := hB.finite_normTwoShell.fintype
  have hsp : (hB.normTwoShellRootPairing k).rootSpan k = ⊤ := by
    refine top_unique ?_
    rw [← (Pi.basisFun k I).span_eq]
    refine span_mono ?_
    rintro _ ⟨i, rfl⟩
    refine ⟨⟨_, single_mem_normTwoShell (hdiag i)⟩, ?_⟩
    ext j
    simp [Pi.single_apply]
  exact ⟨hsp, ((hB.normTwoShellRootPairing k).rootSpan_eq_top_iff).mp hsp⟩

/-- The root system of the norm-two shell is reduced: two linearly dependent roots have pairing
`± 2` with each other, so they are equal or opposite. -/
instance : (hB.normTwoShellRootPairing k).IsReduced where
  eq_or_eq_neg a b h := by
    have := hB.finite_normTwoShell.to_subtype
    set P := hB.normTwoShellRootPairing k
    have h4 := (P.coxeterWeight_eq_four_iff_not_linearIndependent (i := a) (j := b)).mpr h
    have hsymm : b.1 ⬝ᵥ B *ᵥ a.1 = a.1 ⬝ᵥ B *ᵥ b.1 := hB.isHermitian.isSymm.dotProduct_mulVec_comm
    rw [RootPairing.coxeterWeight, pairing_normTwoShellRootPairing,
      pairing_normTwoShellRootPairing, hsymm, ← Int.cast_mul,
      show (4 : k) = ((4 : ℤ) : k) by norm_num, Int.cast_inj] at h4
    have h2 : a.1 ⬝ᵥ B *ᵥ b.1 = 2 ∨ a.1 ⬝ᵥ B *ᵥ b.1 = -2 := by
      have : (a.1 ⬝ᵥ B *ᵥ b.1 - 2) * (a.1 ⬝ᵥ B *ᵥ b.1 + 2) = 0 := by linear_combination h4
      rcases mul_eq_zero.mp this with h | h
      · exact .inl (by linarith)
      · exact .inr (by linarith)
    rcases h2 with h2 | h2
    · exact .inl (congrArg _ (Subtype.ext ((hB.dotProduct_mulVec_eq_two_iff a.2 b.2).mp h2)))
    · right
      rw [normTwoShellRootPairing_root, normTwoShellRootPairing_root,
        (hB.dotProduct_mulVec_eq_neg_two_iff a.2 b.2).mp h2]
      ext i
      simp

/-- The root of the coordinate vector `Pi.single i 1` is the coordinate vector of `I → k`. -/
theorem normTwoShellRootPairing_root_normTwoShellSimple (i : I) :
    (hB.normTwoShellRootPairing k).root (normTwoShellSimple hdiag i) = Pi.single i 1 := by
  ext j
  simp [Pi.single_apply]

/-- A root is the combination of the simple roots with the coefficients of its integer vector. -/
theorem normTwoShellRootPairing_root_eq_sum (a : B.normTwoShell) :
    (hB.normTwoShellRootPairing k).root a =
      ∑ i, a.1 i • (hB.normTwoShellRootPairing k).root (normTwoShellSimple hdiag i) := by
  ext j
  simp [Finset.sum_apply, Pi.single_apply]

/-- A coroot is the combination of the simple coroots with the coefficients of the integer vector
of its root. -/
theorem normTwoShellRootPairing_coroot_eq_sum (a : B.normTwoShell) :
    (hB.normTwoShellRootPairing k).coroot a =
      ∑ i, a.1 i • (hB.normTwoShellRootPairing k).coroot (normTwoShellSimple hdiag i) := by
  ext j
  simp [Finset.sum_apply, mulVec, dotProduct, Pi.single_apply, mul_comm]

variable (hoff : ∀ i j, i ≠ j → B i j ≤ 0)

/-- **The base of coordinate vectors.** When the off-diagonal entries of `B` are nonpositive, the
coordinate vectors form a base of the root system of the norm-two shell: they are linearly
independent, pair nonpositively with one another, and every root and coroot is an integral
combination of the simple ones. -/
def normTwoShellBase : (hB.normTwoShellRootPairing k).Base :=
  have := hB.finite_normTwoShell.to_subtype
  RootPairing.Base.mkOfPairwiseLEZero (hB.normTwoShellRootPairing k)
    (s := Finset.univ.image (normTwoShellSimple hdiag))
    (by
      rw [Finset.coe_image, Finset.coe_univ, image_univ,
        linearIndepOn_range_iff (normTwoShellSimple_injective hdiag)]
      convert (Pi.basisFun k I).linearIndependent using 1
      ext i : 1
      rw [Function.comp_apply, normTwoShellRootPairing_root_normTwoShellSimple,
        Pi.basisFun_apply])
    (by
      rintro _ ha _ hb hab
      rw [Finset.coe_image, Finset.coe_univ, image_univ] at ha hb
      obtain ⟨i, rfl⟩ := ha
      obtain ⟨j, rfl⟩ := hb
      have hij : i ≠ j := fun h ↦ hab (h ▸ rfl)
      simpa [mulVec_single_one, single_one_dotProduct] using hoff i j hij)
    (fun a ↦ by
      rw [normTwoShellRootPairing_coroot_eq_sum hB k hdiag]
      exact sum_mem fun i _ ↦ zsmul_mem (subset_span (mem_image_of_mem _ (by simp))) _)
    (fun a ↦ by
      rw [normTwoShellRootPairing_root_eq_sum hB k hdiag]
      exact sum_mem fun i _ ↦ zsmul_mem (subset_span (mem_image_of_mem _ (by simp))) _)

/-- The simple roots of `Matrix.PosDef.normTwoShellBase` are the coordinate vectors. -/
@[simp]
theorem mem_normTwoShellBase_support {a : B.normTwoShell} :
    a ∈ (hB.normTwoShellBase k hdiag hoff).support ↔ ∃ i, normTwoShellSimple hdiag i = a := by
  have := hB.finite_normTwoShell.to_subtype
  have hs : (hB.normTwoShellBase k hdiag hoff).support =
      Finset.univ.image (normTwoShellSimple hdiag) :=
    RootPairing.Base.mkOfPairwiseLEZero_support _ _ _ _ _
  simp [hs]

/-- **The vertices index the simple roots**: `i` is sent to the coordinate vector `Pi.single i 1`.
-/
def normTwoShellBaseEquiv : I ≃ (hB.normTwoShellBase k hdiag hoff).support :=
  Equiv.ofBijective
    (fun i ↦ ⟨normTwoShellSimple hdiag i, (mem_normTwoShellBase_support hB k hdiag hoff).mpr
      ⟨i, rfl⟩⟩)
    ⟨fun _ _ h ↦ normTwoShellSimple_injective hdiag (congrArg Subtype.val h), fun a ↦ by
      obtain ⟨i, hi⟩ := (mem_normTwoShellBase_support hB k hdiag hoff).mp a.2
      exact ⟨i, Subtype.ext hi⟩⟩

@[simp]
theorem coe_normTwoShellBaseEquiv_apply (i : I) :
    (hB.normTwoShellBaseEquiv k hdiag hoff i : B.normTwoShell) = normTwoShellSimple hdiag i :=
  (rfl)

/-- **The Cartan matrix of the base of coordinate vectors is `B`.** -/
theorem normTwoShellBase_cartanMatrix (i j : I) :
    (hB.normTwoShellBase k hdiag hoff).cartanMatrix (hB.normTwoShellBaseEquiv k hdiag hoff i)
      (hB.normTwoShellBaseEquiv k hdiag hoff j) = B i j := by
  rw [RootPairing.Base.cartanMatrix, RootPairing.Base.cartanMatrixIn_def,
    pairingIn_normTwoShellRootPairing, coe_normTwoShellBaseEquiv_apply,
    coe_normTwoShellBaseEquiv_apply, coe_normTwoShellSimple, coe_normTwoShellSimple,
    mulVec_single_one, single_one_dotProduct, col_apply]

include hdiag hoff in
/-- **The root system of the norm-two shell is irreducible when the diagram of `B` is connected.**
The diagram of the base of coordinate vectors is the diagram of `B`, its Cartan matrix. -/
theorem isIrreducible_normTwoShellRootPairing (hconn : (TauCeti.diagramGraph B).Connected) :
    (hB.normTwoShellRootPairing k).IsIrreducible := by
  have := isRootSystem_normTwoShellRootPairing hB k hdiag
  let e := hB.normTwoShellBaseEquiv k hdiag hoff
  let φ : TauCeti.diagramGraph B ≃g
      TauCeti.diagramGraph (hB.normTwoShellBase k hdiag hoff).cartanMatrix := by
    refine ⟨e, fun {i j} ↦ ?_⟩
    simp only [TauCeti.diagramGraph_adj, e,
      (hB.normTwoShellBaseEquiv k hdiag hoff).injective.ne_iff, normTwoShellBase_cartanMatrix]
  exact RootPairing.isIrreducible_of_connected_diagramGraph_cartanMatrix _
    (φ.connected_iff.mp hconn)

end PosDef

end Matrix
