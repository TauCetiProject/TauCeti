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
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Diagram
public import TauCeti.LinearAlgebra.RootSystem.InvariantSubmodule
public import TauCeti.LinearAlgebra.RootSystem.Reduced

/-!
# The root system of the norm-two shell

Let `B` be a positive definite integer matrix indexed by a finite type `I`, read as the Gram
matrix of the lattice `I → ℤ` with the pairing `⟪a, b⟫ = a ⬝ᵥ B *ᵥ b`. Its norm-two shell
`Φ = {a | ⟪a, a⟫ = 2}` (`Matrix.normTwoShell`) is a finite set, stable under the reflections
`x ↦ x - ⟪x, a⟫ a` in its own vectors. This file makes it a root pairing: over a domain `k` of
characteristic zero, the vectors of `Φ` are the roots in `I → k`, the vector `B *ᵥ a` is the coroot
of the root `a`, and the pairing of `M = N = I → k` is the dot product, so that the Cartan integer
of two roots is their lattice pairing `⟪a, b⟫`.

The root pairing is indexed by `Φ` itself, so by construction its roots are exactly the integral
vectors of norm two. It is crystallographic and reduced. When the diagonal entries of `B` are `2`
the coordinate vectors are roots, and over a field it is a root system spanning `I → k`. When
moreover the off-diagonal entries of `B` are nonpositive, as for the Cartan matrix of a simply
laced Dynkin diagram or the symmetrized Cartan matrix `2I - (A + Aᵀ)` of a quiver with positive
definite Tits form, the coordinate vectors form a base whose Cartan matrix is `B` itself, and the
root system is irreducible when the diagram of `B` is connected. This irreducibility only needs
diagonal `2`, independently of the sign condition on the off-diagonal entries.

## Main definitions

* `Matrix.PosDef.normTwoShellRootPairing`: the root pairing on the norm-two shell.
* `Matrix.PosDef.normTwoShellBase`: the base of coordinate vectors, for nonpositive off-diagonal
  entries.
* `Matrix.PosDef.normTwoShellBaseEquiv`: the vertices `I` index the simple roots of this base.

## Main results

* `Matrix.PosDef.exists_root_normTwoShellRootPairing_eq_iff`: an integral vector is a root
  exactly when it belongs to the norm-two shell.
* `Matrix.PosDef.pairingIn_normTwoShellRootPairing`: the Cartan integer of two roots is their
  lattice pairing.
* `Matrix.PosDef.isRootSystem_normTwoShellRootPairing`: for diagonal `2`, the roots and coroots
  span.
* `Matrix.PosDef.height_normTwoShellBase`: the height is the sum of the integer coordinates.
* `Matrix.PosDef.isPos_normTwoShellBase_iff`: positive roots are the nonnegative shell vectors.
* `Matrix.PosDef.cartanMatrix_normTwoShellBase`: the Cartan matrix of the base is `B`.
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

private theorem piAlgebraMap_dotProduct {I k : Type*} [Fintype I] [CommRing k]
    (a b : I → ℤ) :
    Pi.algebraMap I ℤ k a ⬝ᵥ Pi.algebraMap I ℤ k b = ((a ⬝ᵥ b : ℤ) : k) :=
  (RingHom.map_dotProduct (Int.castRingHom k) a b).symm

namespace PosDef

variable {I : Type*} [Fintype I] {B : Matrix I I ℤ}

section Domain

variable (hB : B.PosDef) (k : Type*) [CommRing k] [CharZero k]

/-- The roots of the norm-two shell, as vectors of `I → k`. -/
private def shellRoot : B.normTwoShell ↪ (I → k) :=
  ⟨fun a ↦ Pi.algebraMap I ℤ k a.1, fun _ _ h ↦ Subtype.ext (TauCeti.piAlgebraMap_injective k h)⟩

private theorem shellRoot_apply (a : B.normTwoShell) :
    shellRoot k a = Pi.algebraMap I ℤ k a.1 := (rfl)

include hB in
/-- The coroots of the norm-two shell, the vectors `B *ᵥ a` of `I → k`; they are distinct because
`B` is nondegenerate. -/
private def shellCoroot : B.normTwoShell ↪ (I → k) :=
  ⟨fun a ↦ Pi.algebraMap I ℤ k (B *ᵥ a.1),
    fun _ _ h ↦ Subtype.ext (hB.mulVec_injective (TauCeti.piAlgebraMap_injective k h))⟩

private theorem shellCoroot_apply (a : B.normTwoShell) :
    shellCoroot hB k a = Pi.algebraMap I ℤ k (B *ᵥ a.1) := (rfl)

variable [IsDomain k] (hdiag : ∀ i, B i i = 2)

/-- **The root pairing of the norm-two shell.** For a positive definite integer matrix `B`, the
vectors `a` with `a ⬝ᵥ B *ᵥ a = 2`, read in `I → k`, are the roots, and the vector `B *ᵥ a` is the
coroot of the root `a`, for the dot product pairing of `I → k` with itself. Reflection in a root
`a` is `x ↦ x - ⟪x, a⟫ a`, which preserves the lattice form and hence the shell. -/
def normTwoShellRootPairing : RootPairing B.normTwoShell k (I → k) (I → k) :=
  haveI := hB.finite_normTwoShell.to_subtype
  RootPairing.mk' (dotProductBilin k k) (shellRoot k) (shellCoroot hB k)
    (fun a ↦ by
      rw [dotProductBilin_apply_apply, shellRoot_apply, shellCoroot_apply,
        piAlgebraMap_dotProduct, mem_normTwoShell.mp a.2, Int.cast_ofNat])
    (by
      rintro a - ⟨b, rfl⟩
      refine ⟨⟨_, hB.isHermitian.isSymm.sub_smul_mem_normTwoShell a.2 b.2⟩, ?_⟩
      simp only [preReflection_apply, LinearMap.flip_apply, dotProductBilin_apply_apply,
        shellRoot_apply, shellCoroot_apply, piAlgebraMap_dotProduct, map_sub, map_zsmul,
        Int.cast_smul_eq_zsmul])
    (by
      rintro a - ⟨b, rfl⟩
      refine ⟨⟨_, hB.isHermitian.isSymm.sub_smul_mem_normTwoShell a.2 b.2⟩, ?_⟩
      simp only [preReflection_apply, dotProductBilin_apply_apply,
        shellRoot_apply, shellCoroot_apply, piAlgebraMap_dotProduct, mulVec_sub, mulVec_smul,
        map_sub, map_zsmul, Int.cast_smul_eq_zsmul,
        hB.isHermitian.isSymm.dotProduct_mulVec_comm (x := b.1) (y := a.1)])

@[simp]
theorem root_normTwoShellRootPairing (a : B.normTwoShell) :
    (hB.normTwoShellRootPairing k).root a = fun i ↦ (a.1 i : k) :=
  (rfl)

/-- An integral vector occurs as a root exactly when it belongs to the norm-two shell. -/
theorem exists_root_normTwoShellRootPairing_eq_iff (d : I → ℤ) :
    (∃ a, (hB.normTwoShellRootPairing k).root a = fun i ↦ (d i : k)) ↔ d ∈ B.normTwoShell := by
  constructor
  · rintro ⟨a, ha⟩
    rw [root_normTwoShellRootPairing] at ha
    have had : a.1 = d := TauCeti.piAlgebraMap_injective k ha
    exact had ▸ a.2
  · intro hd
    exact ⟨⟨d, hd⟩, root_normTwoShellRootPairing hB k _⟩

@[simp]
theorem coroot_normTwoShellRootPairing (a : B.normTwoShell) :
    (hB.normTwoShellRootPairing k).coroot a = fun i ↦ ((B *ᵥ a.1) i : k) :=
  (rfl)

@[simp]
theorem toLinearMap_normTwoShellRootPairing (x y : I → k) :
    (hB.normTwoShellRootPairing k).toLinearMap x y = x ⬝ᵥ y :=
  (rfl)

/-- The pairing of two roots of the norm-two shell is their lattice pairing. -/
@[simp]
theorem pairing_normTwoShellRootPairing (a b : B.normTwoShell) :
    (hB.normTwoShellRootPairing k).pairing a b = ((a.1 ⬝ᵥ B *ᵥ b.1 : ℤ) : k) := by
  rw [RootPairing.pairing, toLinearMap_normTwoShellRootPairing,
    root_normTwoShellRootPairing, coroot_normTwoShellRootPairing]
  exact piAlgebraMap_dotProduct _ _

/-- Reflection in a shell root acts by the integral lattice reflection. -/
@[simp]
theorem coe_reflectionPerm_normTwoShellRootPairing (a b : B.normTwoShell) :
    ((hB.normTwoShellRootPairing k).reflectionPerm a b : I → ℤ) =
      b.1 - (b.1 ⬝ᵥ B *ᵥ a.1) • a.1 := by
  apply TauCeti.piAlgebraMap_injective k
  have h := (hB.normTwoShellRootPairing k).reflectionPerm_root a b
  rw [RootPairing.root_coroot_eq_pairing, pairing_normTwoShellRootPairing] at h
  simp only [root_normTwoShellRootPairing] at h
  ext i
  simpa [TauCeti.piAlgebraMap_apply] using congrFun h.symm i

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
/-- The coordinate vectors are roots for diagonal `2`, so the roots span over any domain. -/
@[simp]
theorem rootSpan_normTwoShellRootPairing : (hB.normTwoShellRootPairing k).rootSpan k = ⊤ :=
  TauCeti.span_range_piAlgebraMap_eq_top k
    (v := (Subtype.val : B.normTwoShell → I → ℤ))
    (by rw [Subtype.range_val]; exact B.span_normTwoShell_eq_top_of_diagonal_eq_two hdiag)

/-- The root pairing of the norm-two shell is reduced: two linearly dependent roots have pairing
`± 2` with each other, so they are equal or opposite. -/
instance : (hB.normTwoShellRootPairing k).IsReduced :=
  RootPairing.isReduced_of_pairing_comm _ fun a b ↦ by
    rw [pairing_normTwoShellRootPairing, pairing_normTwoShellRootPairing,
      hB.isHermitian.isSymm.dotProduct_mulVec_comm]

variable [DecidableEq I]

/-- The root of the coordinate vector `Pi.single i 1` is the coordinate vector of `I → k`. -/
theorem root_normTwoShellRootPairing_normTwoShellSimple (i : I) :
    (hB.normTwoShellRootPairing k).root (normTwoShellSimple hdiag i) = Pi.single i 1 := by
  ext j
  simp [Pi.single_apply]

/-- A root is the combination of the simple roots with the coefficients of its integer vector. -/
theorem root_normTwoShellRootPairing_eq_sum (a : B.normTwoShell) :
    (hB.normTwoShellRootPairing k).root a =
      ∑ i, a.1 i • (hB.normTwoShellRootPairing k).root (normTwoShellSimple hdiag i) := by
  ext j
  simp [Finset.sum_apply, Pi.single_apply]

/-- A coroot is the combination of the simple coroots with the coefficients of the integer vector
of its root. -/
theorem coroot_normTwoShellRootPairing_eq_sum (a : B.normTwoShell) :
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
      rw [Function.comp_apply, root_normTwoShellRootPairing_normTwoShellSimple,
        Pi.basisFun_apply])
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

/-- The simple roots of `Matrix.PosDef.normTwoShellBase` are the coordinate vectors. -/
theorem mem_normTwoShellBase_support {a : B.normTwoShell} :
    a ∈ (hB.normTwoShellBase k hdiag hoff).support ↔ ∃ i, normTwoShellSimple hdiag i = a := by
  simp [support_normTwoShellBase]

/-- Every coordinate vector belongs to the support of the coordinate base. -/
theorem normTwoShellSimple_mem_normTwoShellBase_support (i : I) :
    normTwoShellSimple hdiag i ∈ (hB.normTwoShellBase k hdiag hoff).support := by
  simp

/-- **The vertices index the simple roots**: `i` is sent to the coordinate vector `Pi.single i 1`.
-/
def normTwoShellBaseEquiv : I ≃ (hB.normTwoShellBase k hdiag hoff).support :=
  (Equiv.ofInjective _ (normTwoShellSimple_injective hdiag)).trans
    (.subtypeEquivRight fun _ ↦ by simp)

@[simp]
theorem coe_normTwoShellBaseEquiv_apply (i : I) :
    (hB.normTwoShellBaseEquiv k hdiag hoff i : B.normTwoShell) = normTwoShellSimple hdiag i :=
  (rfl)

/-- The inverse vertex equivalence recovers the index of a coordinate vector. -/
@[simp]
theorem normTwoShellBaseEquiv_symm_mk (i : I)
    (hi : normTwoShellSimple hdiag i ∈ (hB.normTwoShellBase k hdiag hoff).support) :
    (hB.normTwoShellBaseEquiv k hdiag hoff).symm ⟨normTwoShellSimple hdiag i, hi⟩ = i :=
  (hB.normTwoShellBaseEquiv k hdiag hoff).symm_apply_apply i

/-- The height relative to the coordinate base is the sum of the integer coordinates. -/
@[simp]
theorem height_normTwoShellBase (a : B.normTwoShell) :
    (hB.normTwoShellBase k hdiag hoff).height a = ∑ i, a.1 i := by
  have hs := hB.support_normTwoShellBase k hdiag hoff
  have hinj := (normTwoShellSimple_injective hdiag).injOn (s := (Finset.univ : Finset I))
  have hexp : (hB.normTwoShellRootPairing k).root a =
      ∑ b ∈ (hB.normTwoShellBase k hdiag hoff).support,
        (a.1 ⬝ᵥ b.1) • (hB.normTwoShellRootPairing k).root b := by
    rw [hs, Finset.sum_image hinj]
    simpa using hB.root_normTwoShellRootPairing_eq_sum k hdiag a
  rw [RootPairing.Base.height_eq_sum hexp, hs, Finset.sum_image hinj]
  simp

/-- A shell root is positive relative to the coordinate base exactly when it is nonnegative. -/
@[simp]
theorem isPos_normTwoShellBase_iff (a : B.normTwoShell) :
    (hB.normTwoShellBase k hdiag hoff).IsPos a ↔ 0 ≤ a.1 := by
  rw [RootPairing.Base.isPos_iff', height_normTwoShellBase]
  constructor
  · intro hsum
    rcases hB.nonneg_or_nonpos_of_mem_normTwoShell (fun i ↦ hdiag i ▸ even_two) hoff a.2 with
      hpos | hneg
    · exact hpos
    · have hzero : ∑ i, a.1 i = 0 := le_antisymm (Finset.sum_nonpos fun i _ ↦ hneg i) hsum
      exact fun i ↦ ((Finset.sum_eq_zero_iff_of_nonpos (fun j _ ↦ hneg j)).mp hzero i
        (Finset.mem_univ i)).ge
  · exact fun hpos ↦ Finset.sum_nonneg fun i _ ↦ hpos i

/-- **The Cartan matrix of the base of coordinate vectors is `B`.** -/
@[simp]
theorem cartanMatrix_normTwoShellBase (i j : I) :
    (hB.normTwoShellBase k hdiag hoff).cartanMatrix (hB.normTwoShellBaseEquiv k hdiag hoff i)
      (hB.normTwoShellBaseEquiv k hdiag hoff j) = B i j := by
  simp [RootPairing.Base.cartanMatrix, RootPairing.Base.cartanMatrixIn_def]

end Domain

variable (hB : B.PosDef) (k : Type*) [Field k] [CharZero k]
  (hdiag : ∀ i, B i i = 2)

include hdiag in
/-- Over a field the roots and coroots span once the diagonal entries are `2`. -/
theorem isRootSystem_normTwoShellRootPairing : (hB.normTwoShellRootPairing k).IsRootSystem := by
  have := hB.finite_normTwoShell.fintype
  have hsp := hB.rootSpan_normTwoShellRootPairing k hdiag
  exact ⟨hsp, ((hB.normTwoShellRootPairing k).rootSpan_eq_top_iff).mp hsp⟩

include hdiag in
/-- **The root system of the norm-two shell is irreducible when the diagram of `B` is connected.**
No sign condition on the off-diagonal entries is needed. -/
theorem isIrreducible_normTwoShellRootPairing (hconn : (TauCeti.diagramGraph B).Connected) :
    (hB.normTwoShellRootPairing k).IsIrreducible := by
  classical
  have := isRootSystem_normTwoShellRootPairing hB k hdiag
  let P := hB.normTwoShellRootPairing k
  let _ : Nontrivial (I → k) :=
    ⟨⟨P.root (normTwoShellSimple hdiag hconn.nonempty.some), 0, P.ne_zero _⟩⟩
  apply RootPairing.IsIrreducible.mk' P
  intro q hinv hq
  -- A subspace missing all coordinate roots lies in their coroot kernels, hence in every
  -- coroot kernel, since every coroot is an integral combination of coordinate coroots.
  have hsimple : ∃ i, P.root (normTwoShellSimple hdiag i) ∈ q := by
    by_contra! h
    apply hq
    apply eq_bot_iff.mpr
    intro x hx
    apply P.eq_zero_iff_forall_coroot'_eq_zero.mpr
    have hz (i : I) : P.coroot' (normTwoShellSimple hdiag i) x = 0 :=
      LinearMap.mem_ker.mp (RootPairing.invtRootSubmodule.le_ker_coroot'
        ⟨q, P.mem_invtRootSubmodule_iff.mpr hinv⟩ (h i) hx)
    intro a
    rw [RootPairing.coroot', LinearMap.flip_apply,
      coroot_normTwoShellRootPairing_eq_sum hB k hdiag a]
    simp only [map_sum, map_zsmul]
    exact Finset.sum_eq_zero fun i _ ↦ by
      have hi := hz i
      rw [RootPairing.coroot', LinearMap.flip_apply] at hi
      rw [hi, smul_zero]
  obtain ⟨i, hi⟩ := hsimple
  -- Nonzero Gram entries propagate membership along diagram walks; the coordinate roots span.
  have propagate {u v : I} (hadj : (TauCeti.diagramGraph B).Adj u v)
      (hu : P.root (normTwoShellSimple hdiag u) ∈ q) :
      P.root (normTwoShellSimple hdiag v) ∈ q := by
    apply RootPairing.root_mem_of_isUnit_pairing (hinv _) _ hu
    apply Ne.isUnit
    simpa [P] using (Int.cast_ne_zero.mpr (TauCeti.diagramGraph_adj.mp hadj).2.1 : (B u v : k) ≠ 0)
  have hall (j : I) : P.root (normTwoShellSimple hdiag j) ∈ q := by
    obtain ⟨w⟩ := hconn.preconnected i j
    let rec along {u v : I} (w : (TauCeti.diagramGraph B).Walk u v)
        (hu : P.root (normTwoShellSimple hdiag u) ∈ q) :
        P.root (normTwoShellSimple hdiag v) ∈ q :=
      match w with
      | .nil => hu
      | .cons hadj w => along w (propagate hadj hu)
    exact along w hi
  rw [eq_top_iff, ← (Pi.basisFun k I).span_eq]
  refine span_le.mpr ?_
  rintro _ ⟨j, rfl⟩
  rw [Pi.basisFun_apply, ← root_normTwoShellRootPairing_normTwoShellSimple hB k hdiag]
  exact hall j

end PosDef

end Matrix
