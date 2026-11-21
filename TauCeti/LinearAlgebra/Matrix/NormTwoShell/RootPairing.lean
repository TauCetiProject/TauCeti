/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Irreducible
public import TauCeti.LinearAlgebra.Matrix.Dual
public import TauCeti.LinearAlgebra.Matrix.NormTwoShell.Basic
public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Pi
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Irreducible
public import TauCeti.LinearAlgebra.RootSystem.Reduced
import TauCeti.Data.Matrix.DotProduct

/-!
# The root system of the norm-two shell

Let `B` be a positive definite integer matrix indexed by a finite type `I`, read as the Gram
matrix of the lattice `I → ℤ` with the pairing `⟪a, b⟫ = a ⬝ᵥ B *ᵥ b`. Its norm-two shell
`Φ = {a | ⟪a, a⟫ = 2}` (`Matrix.normTwoShell`) is a finite set, stable under the reflections
`x ↦ x - ⟪x, a⟫ a` in its own vectors. This file makes it a root pairing: over a commutative ring
`k` of characteristic zero, the vectors of `Φ` are the roots in `I → k`, the vector `B *ᵥ a` is the
coroot of the root `a`, and the pairing of `M = N = I → k` is the dot product, so that the Cartan
integer of two roots is their lattice pairing `⟪a, b⟫`.

The root pairing is indexed by `Φ` itself, so by construction its roots are exactly the integral
vectors of norm two. It is crystallographic, and reduced over a domain. When `Φ` spans the lattice,
for instance when the diagonal entries of `B` are `2` so that the coordinate vectors are roots, the
roots span `I → k`, and over a field it is a root system. When
moreover the off-diagonal entries of `B` are nonpositive, as for the Cartan matrix of a simply
laced Dynkin diagram or the symmetrized Cartan matrix `2I - (A + Aᵀ)` of a quiver with positive
definite Tits form, the coordinate vectors form a base whose Cartan matrix is `B` itself, and the
root system is irreducible when the diagram of `B` is connected. This irreducibility only needs
diagonal `2`, independently of the sign condition on the off-diagonal entries.

## Main definitions

* `Matrix.PosDef.normTwoShellRootPairing`: the root pairing on the norm-two shell.
* `Matrix.PosDef.normTwoShellBase`: the base of coordinate vectors of the root pairing, for
  diagonal `2` and nonpositive off-diagonal entries.
* `Matrix.PosDef.normTwoShellBaseEquiv`: the vertices `I` index the simple roots of this base.

## Main results

* `Matrix.PosDef.exists_root_normTwoShellRootPairing_eq_iff`: an integral vector is a root
  exactly when it belongs to the norm-two shell.
* `Matrix.PosDef.pairingIn_normTwoShellRootPairing`: the Cartan integer of two roots is their
  lattice pairing.
* `Matrix.PosDef.isRootSystem_normTwoShellRootPairing`: over a field, the roots and coroots span
  when the norm-two shell spans the lattice, for instance for diagonal `2`.
* `Matrix.PosDef.height_normTwoShellBase`: the height is the sum of the integer coordinates.
* `Matrix.PosDef.isPos_normTwoShellBase_iff`: positive roots are the nonnegative shell vectors.
* `Matrix.PosDef.cartanMatrix_normTwoShellBase`: the Cartan matrix of the base is `B`.
* `Matrix.PosDef.isIrreducible_normTwoShellRootPairing`: over a field and for diagonal `2`, the
  root system is irreducible when the diagram of `B` is connected.

## References

* I. N. Bernstein, I. M. Gelfand and V. A. Ponomarev, *Coxeter functors and Gabriel's theorem*,
  Russian Math. Surveys 28 (1973), §2, where the roots of a positive definite integral quadratic
  form are made a root system in this way.
* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, Proposition 5.10.
-/

public noncomputable section

open Function Set Module Submodule

namespace Matrix

namespace PosDef

variable {I : Type*} [Fintype I] {B : Matrix I I ℤ}

section CommRing

variable (hB : B.PosDef) (k : Type*) [CommRing k] [CharZero k]

/-- The roots of the norm-two shell, as vectors of `I → k`. -/
private def shellRoot : B.normTwoShell ↪ (I → k) :=
  ⟨fun a i ↦ (a.val i : k), fun _ _ h ↦ Subtype.ext (Int.cast_injective.comp_left h)⟩

private theorem shellRoot_apply (a : B.normTwoShell) :
    shellRoot k a = fun i ↦ (a.val i : k) := (rfl)

include hB in
/-- The coroots of the norm-two shell, the vectors `B *ᵥ a` of `I → k`; they are distinct because
`B` is nondegenerate. -/
private def shellCoroot : B.normTwoShell ↪ (I → k) :=
  ⟨fun a i ↦ ((B *ᵥ a.val) i : k),
    fun _ _ h ↦ Subtype.ext (hB.mulVec_injective (Int.cast_injective.comp_left h))⟩

private theorem shellCoroot_apply (a : B.normTwoShell) :
    shellCoroot hB k a = fun i ↦ ((B *ᵥ a.val) i : k) := (rfl)

include hB in
/-- Reflection of the norm-two shell in its vector `a`, the involution `b ↦ b - ⟪b, a⟫ a`. -/
private def shellReflection (a : B.normTwoShell) : Equiv.Perm B.normTwoShell :=
  Involutive.toPerm
    (fun b ↦ ⟨b.val - (b.val ⬝ᵥ B *ᵥ a.val) • a.val,
      hB.isHermitian.isSymm.sub_smul_mem_normTwoShell a.property b.property⟩)
    fun b ↦ Subtype.ext <| by
      have ha : a.val ⬝ᵥ B *ᵥ a.val = 2 := mem_normTwoShell.mp a.property
      ext i
      simp only [sub_dotProduct, smul_dotProduct, ha, smul_eq_mul, Pi.sub_apply, Pi.smul_apply]
      ring

private theorem coe_shellReflection_apply (a b : B.normTwoShell) :
    (shellReflection hB a b : I → ℤ) = b.val - (b.val ⬝ᵥ B *ᵥ a.val) • a.val := (rfl)

/-- **The root pairing of the norm-two shell.** For a positive definite integer matrix `B`, the
vectors `a` with `a ⬝ᵥ B *ᵥ a = 2`, read in `I → k`, are the roots, and the vector `B *ᵥ a` is the
coroot of the root `a`, for the dot product pairing of `I → k` with itself. Reflection in a root
`a` is `x ↦ x - ⟪x, a⟫ a`, which preserves the lattice form and hence the shell. -/
def normTwoShellRootPairing : RootPairing B.normTwoShell k (I → k) (I → k) where
  toLinearMap := dotProductBilin k k
  root := shellRoot k
  coroot := shellCoroot hB k
  root_coroot_two a := by
    rw [dotProductBilin_apply_apply, shellRoot_apply, shellCoroot_apply, intCast_dotProduct,
      mem_normTwoShell.mp a.property, Int.cast_ofNat]
  reflectionPerm := shellReflection hB
  reflectionPerm_root a b := by
    simp only [dotProductBilin_apply_apply, shellRoot_apply, shellCoroot_apply, intCast_dotProduct,
      coe_shellReflection_apply]
    ext i
    simp
  reflectionPerm_coroot a b := by
    simp only [dotProductBilin_apply_apply, shellRoot_apply, shellCoroot_apply, intCast_dotProduct,
      coe_shellReflection_apply, mulVec_sub, mulVec_smul,
      hB.isHermitian.isSymm.dotProduct_mulVec_comm (x := a.val) (y := b.val)]
    ext i
    simp

@[simp]
theorem root_normTwoShellRootPairing (a : B.normTwoShell) :
    (hB.normTwoShellRootPairing k).root a = fun i ↦ (a.val i : k) :=
  (rfl)

/-- An integral vector occurs as a root exactly when it belongs to the norm-two shell. -/
theorem exists_root_normTwoShellRootPairing_eq_iff (d : I → ℤ) :
    (∃ a, (hB.normTwoShellRootPairing k).root a = fun i ↦ (d i : k)) ↔ d ∈ B.normTwoShell := by
  constructor
  · rintro ⟨a, ha⟩
    rw [root_normTwoShellRootPairing] at ha
    have had : a.val = d := Int.cast_injective.comp_left ha
    exact had ▸ a.property
  · intro hd
    exact ⟨⟨d, hd⟩, root_normTwoShellRootPairing hB k _⟩

@[simp]
theorem coroot_normTwoShellRootPairing (a : B.normTwoShell) :
    (hB.normTwoShellRootPairing k).coroot a = fun i ↦ ((B *ᵥ a.val) i : k) :=
  (rfl)

@[simp]
theorem toLinearMap_normTwoShellRootPairing (x y : I → k) :
    (hB.normTwoShellRootPairing k).toLinearMap x y = x ⬝ᵥ y :=
  dotProductBilin_apply_apply k k x y

/-- The pairing of two roots of the norm-two shell is their lattice pairing. -/
@[simp]
theorem pairing_normTwoShellRootPairing (a b : B.normTwoShell) :
    (hB.normTwoShellRootPairing k).pairing a b = ((a.val ⬝ᵥ B *ᵥ b.val : ℤ) : k) := by
  rw [RootPairing.pairing, toLinearMap_normTwoShellRootPairing,
    root_normTwoShellRootPairing, coroot_normTwoShellRootPairing, intCast_dotProduct]

/-- Reflection in a shell root acts by the integral lattice reflection. -/
@[simp]
theorem coe_reflectionPerm_normTwoShellRootPairing (a b : B.normTwoShell) :
    ((hB.normTwoShellRootPairing k).reflectionPerm a b : I → ℤ) =
      b.val - (b.val ⬝ᵥ B *ᵥ a.val) • a.val :=
  coe_shellReflection_apply hB a b

instance : (hB.normTwoShellRootPairing k).IsCrystallographic where
  exists_value a b := ⟨a.val ⬝ᵥ B *ᵥ b.val, by
    rw [pairing_normTwoShellRootPairing, algebraMap_int_eq, eq_intCast]⟩

/-- **The Cartan integer of two roots of the norm-two shell is their lattice pairing.** -/
@[simp]
theorem pairingIn_normTwoShellRootPairing (a b : B.normTwoShell) :
    (hB.normTwoShellRootPairing k).pairingIn ℤ a b = a.val ⬝ᵥ B *ᵥ b.val := by
  apply FaithfulSMul.algebraMap_injective ℤ k
  rw [RootPairing.algebraMap_pairingIn, pairing_normTwoShellRootPairing, algebraMap_int_eq,
    eq_intCast]

/-- The roots span once the norm-two shell spans the lattice `I → ℤ`. -/
@[simp]
theorem rootSpan_normTwoShellRootPairing_eq_top (hspan : span ℤ B.normTwoShell = ⊤) :
    (hB.normTwoShellRootPairing k).rootSpan k = ⊤ := by
  have hroot : ⇑(hB.normTwoShellRootPairing k).root =
      fun a : B.normTwoShell ↦ Pi.algebraMap I ℤ k a.val := by
    ext a i
    simp [TauCeti.piAlgebraMap_apply]
  rw [RootPairing.rootSpan, hroot]
  exact TauCeti.span_range_piAlgebraMap_eq_top k (by rwa [Subtype.range_val])

variable [DecidableEq I] (hdiag : ∀ i, B i i = 2)

/-- The root of the coordinate vector `Pi.single i 1` is the coordinate vector of `I → k`. -/
theorem root_normTwoShellRootPairing_normTwoShellSimple (i : I) :
    (hB.normTwoShellRootPairing k).root (normTwoShellSimple hdiag i) = Pi.single i 1 := by
  ext j
  simp [Pi.single_apply]

/-- The roots of the coordinate vectors are the standard basis of `I → k`. -/
theorem root_comp_normTwoShellSimple :
    (hB.normTwoShellRootPairing k).root ∘ normTwoShellSimple hdiag = Pi.basisFun k I := by
  ext i : 1
  rw [Function.comp_apply, root_normTwoShellRootPairing_normTwoShellSimple, Pi.basisFun_apply]

/-- A root is the combination of the coordinate roots with the coefficients of its integer
vector. -/
theorem root_normTwoShellRootPairing_eq_sum (a : B.normTwoShell) :
    (hB.normTwoShellRootPairing k).root a =
      ∑ i, a.val i • (hB.normTwoShellRootPairing k).root (normTwoShellSimple hdiag i) := by
  ext j
  simp [Finset.sum_apply, Pi.single_apply]

/-- A coroot is the combination of the coroots of the coordinate roots with the coefficients of
the integer vector of its root. -/
theorem coroot_normTwoShellRootPairing_eq_sum (a : B.normTwoShell) :
    (hB.normTwoShellRootPairing k).coroot a =
      ∑ i, a.val i • (hB.normTwoShellRootPairing k).coroot (normTwoShellSimple hdiag i) := by
  ext j
  simp [Finset.sum_apply, mulVec, dotProduct, Pi.single_apply, mul_comm]

end CommRing

section Domain

variable (hB : B.PosDef) (k : Type*) [CommRing k] [CharZero k] [IsDomain k]

/-- The root pairing of the norm-two shell is reduced. -/
instance : (hB.normTwoShellRootPairing k).IsReduced :=
  RootPairing.isReduced_of_pairing_comm _ fun a b ↦ by
    rw [pairing_normTwoShellRootPairing, pairing_normTwoShellRootPairing,
      hB.isHermitian.isSymm.dotProduct_mulVec_comm]

variable [DecidableEq I] (hdiag : ∀ i, B i i = 2) (hoff : ∀ i j, i ≠ j → B i j ≤ 0)

/-- **The base of coordinate vectors.** When the diagonal entries of `B` are `2` and its
off-diagonal entries are nonpositive, the coordinate vectors form a base of the root pairing of the
norm-two shell. -/
def normTwoShellBase : (hB.normTwoShellRootPairing k).Base :=
  have := hB.finite_normTwoShell.to_subtype
  RootPairing.Base.mkOfPairwiseLEZero (hB.normTwoShellRootPairing k)
    (s := Finset.univ.image (normTwoShellSimple hdiag))
    (by
      rw [Finset.coe_image, Finset.coe_univ, image_univ,
        linearIndepOn_range_iff (normTwoShellSimple_injective hdiag),
        root_comp_normTwoShellSimple]
      exact (Pi.basisFun k I).linearIndependent)
    (by
      rintro _ ha _ hb hab
      rw [Finset.coe_image, Finset.coe_univ, image_univ] at ha hb
      obtain ⟨i, rfl⟩ := ha
      obtain ⟨j, rfl⟩ := hb
      have hij : i ≠ j := fun h ↦ hab (h ▸ rfl)
      simpa [mulVec_single_one, single_one_dotProduct] using hoff i j hij)
    (fun a ↦ by
      rw [coroot_normTwoShellRootPairing_eq_sum hB k hdiag]
      exact sum_mem fun i _ ↦ zsmul_mem (subset_span (mem_image_of_mem _ (by simp))) _)
    (fun a ↦ by
      rw [root_normTwoShellRootPairing_eq_sum hB k hdiag]
      exact sum_mem fun i _ ↦ zsmul_mem (subset_span (mem_image_of_mem _ (by simp))) _)

/-- The support of the coordinate base is the set of coordinate vectors. -/
@[simp]
theorem support_normTwoShellBase :
    (hB.normTwoShellBase k hdiag hoff).support =
      Finset.univ.image (normTwoShellSimple hdiag) := by
  have := hB.finite_normTwoShell.to_subtype
  exact RootPairing.Base.mkOfPairwiseLEZero_support _ _ _ _ _

/-- **The vertices index the simple roots**: `i` is sent to the coordinate vector `Pi.single i 1`.
-/
def normTwoShellBaseEquiv : I ≃ (hB.normTwoShellBase k hdiag hoff).support :=
  (Equiv.ofInjective _ (normTwoShellSimple_injective hdiag)).trans
    (.subtypeEquivRight fun _ ↦ by simp)

@[simp]
theorem coe_normTwoShellBaseEquiv_apply (i : I) :
    (hB.normTwoShellBaseEquiv k hdiag hoff i : B.normTwoShell) = normTwoShellSimple hdiag i := by
  simp [normTwoShellBaseEquiv]

/-- The inverse vertex equivalence recovers the index of a coordinate vector. -/
@[simp]
theorem normTwoShellBaseEquiv_symm_mk (i : I)
    (hi : normTwoShellSimple hdiag i ∈ (hB.normTwoShellBase k hdiag hoff).support) :
    (hB.normTwoShellBaseEquiv k hdiag hoff).symm ⟨normTwoShellSimple hdiag i, hi⟩ = i := by
  rw [Equiv.symm_apply_eq]
  exact Subtype.ext (coe_normTwoShellBaseEquiv_apply hB k hdiag hoff i).symm

/-- The height relative to the coordinate base is the sum of the integer coordinates. -/
@[simp]
theorem height_normTwoShellBase (a : B.normTwoShell) :
    (hB.normTwoShellBase k hdiag hoff).height a = ∑ i, a.val i := by
  have hs := hB.support_normTwoShellBase k hdiag hoff
  have hinj := (normTwoShellSimple_injective hdiag).injOn (s := (Finset.univ : Finset I))
  have hexp : (hB.normTwoShellRootPairing k).root a =
      ∑ b ∈ (hB.normTwoShellBase k hdiag hoff).support,
        (a.val ⬝ᵥ b.val) • (hB.normTwoShellRootPairing k).root b := by
    rw [hs, Finset.sum_image hinj]
    simpa using hB.root_normTwoShellRootPairing_eq_sum k hdiag a
  rw [RootPairing.Base.height_eq_sum hexp, hs, Finset.sum_image hinj]
  simp

/-- A shell root is positive relative to the coordinate base exactly when it is nonnegative. -/
@[simp]
theorem isPos_normTwoShellBase_iff (a : B.normTwoShell) :
    (hB.normTwoShellBase k hdiag hoff).IsPos a ↔ 0 ≤ a.val := by
  constructor
  · intro hsum
    rw [RootPairing.Base.isPos_iff, height_normTwoShellBase] at hsum
    refine (hB.nonneg_or_nonpos_of_mem_normTwoShell (fun i ↦ hdiag i ▸ even_two) hoff
      a.property).resolve_right fun hneg ↦ hsum.not_ge (Finset.sum_nonpos fun i _ ↦ hneg i)
  · intro hpos
    rw [RootPairing.Base.isPos_iff', height_normTwoShellBase]
    exact Finset.sum_nonneg fun i _ ↦ hpos i

/-- **The Cartan matrix of the base of coordinate vectors is `B`.** -/
@[simp]
theorem cartanMatrix_normTwoShellBase (i j : I) :
    (hB.normTwoShellBase k hdiag hoff).cartanMatrix (hB.normTwoShellBaseEquiv k hdiag hoff i)
      (hB.normTwoShellBaseEquiv k hdiag hoff j) = B i j := by
  simp [RootPairing.Base.cartanMatrix, RootPairing.Base.cartanMatrixIn_def]

end Domain

variable (hB : B.PosDef) (k : Type*) [Field k] [CharZero k]

/-- Over a field the roots and coroots span once the norm-two shell spans the lattice `I → ℤ`. -/
theorem isRootSystem_normTwoShellRootPairing (hspan : span ℤ B.normTwoShell = ⊤) :
    (hB.normTwoShellRootPairing k).IsRootSystem := by
  have := hB.finite_normTwoShell.fintype
  have hsp := hB.rootSpan_normTwoShellRootPairing_eq_top k hspan
  exact ⟨hsp, ((hB.normTwoShellRootPairing k).rootSpan_eq_top_iff).mp hsp⟩

/-- **Over a field, for diagonal `2`, the root system of the norm-two shell is irreducible when the
diagram of `B` is connected.** No sign condition on the off-diagonal entries is needed. -/
theorem isIrreducible_normTwoShellRootPairing (hdiag : ∀ i, B i i = 2)
    (hconn : (TauCeti.diagramGraph B).Connected) :
    (hB.normTwoShellRootPairing k).IsIrreducible := by
  classical
  have := isRootSystem_normTwoShellRootPairing hB k (B.span_normTwoShell_eq_top_of_diagonal_eq_two
    hdiag)
  let P := hB.normTwoShellRootPairing k
  have hcoroot : span k (range (P.coroot ∘ normTwoShellSimple hdiag)) = ⊤ := by
    rw [eq_top_iff, ← RootPairing.IsRootSystem.span_coroot_eq_top (P := P), span_le]
    rintro _ ⟨a, rfl⟩
    rw [coroot_normTwoShellRootPairing_eq_sum hB k hdiag a]
    exact sum_mem fun i _ ↦ zsmul_mem (subset_span (mem_range_self i)) _
  have hB' : (Matrix.of fun u v ↦
      P.pairingIn ℤ (normTwoShellSimple hdiag u) (normTwoShellSimple hdiag v)) = B := by
    ext u v
    simp [P]
  refine RootPairing.isIrreducible_of_connected_diagramGraph_pairingIn _ ?_ hcoroot
    (by rwa [hB'])
  rw [root_comp_normTwoShellSimple]
  exact (Pi.basisFun k I).span_eq

end PosDef

end Matrix
