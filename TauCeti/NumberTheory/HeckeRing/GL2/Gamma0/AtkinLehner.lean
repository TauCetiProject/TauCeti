/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Claude
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Basic
public import TauCeti.NumberTheory.HeckeRing.GLn.TransposeAntiInvolution
-- `mem_Gamma0_iff_dvd` and the Γ₀ unit-entry lemma, both only inside proofs.
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic
-- `mem_doubleCoset_natDiagGL_of_intWitness` (Shimura 3.33), used only inside the proof of
-- `atkinLehnerAntiInvolution_bar_mem_doubleCoset_of_coprime_upperLeft` below, so private.
import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.BadPrimeCoset
import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.ElementaryDivisors
import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.CosetMap
import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Diagonal.Coset
import TauCeti.LinearAlgebra.Matrix.SmithNormalForm
import TauCeti.Data.ZMod.Units
import Mathlib.Data.Nat.Prime.Int

/-!
# The Atkin-Lehner anti-involution of the `Γ₀(N)` Hecke pair

Conjugating the transpose by `w = diag(1, N)`,
```
ι(g) = w · gᵀ · w⁻¹,
```
is an anti-automorphism of `GL₂(ℚ)` preserving both the image of `Γ₀(N)` and the submonoid
`Δ₀(N)`, so it restricts to a `HeckeAntiInvolution` of the `Γ₀(N)` Hecke datum.

At level one the transpose alone already does this — that is
`HeckeRing.GLn.transposeAntiInvolution`, and it is why the `GL_n` Hecke ring is commutative.
It does **not** survive the congruence condition: transposition carries `Γ₀(N)` to `Γ⁰(N)`,
swapping which off-diagonal entry is divisible by `N`. Conjugating by `w` swaps it back, which
is exactly what the Atkin-Lehner twist buys.

On entries the map is `(a, b; N c, e) ↦ (a, c; N b, e)`: the lower-left entry stays divisible
by `N`, the determinant is unchanged, and — the point of the construction — the upper-left
entry is untouched, so the coprimality condition cutting out `Δ₀(N)` transfers with no work.
Integrality of the new upper-right entry is precisely the hypothesis `N ∣ A 1 0`.

Beyond the anti-involution itself, this file proves that `ι` preserves determinants and fixes
the double coset of any `x ∈ Δ₀(N)` whose determinant is coprime to the level, or divides a
power of it. These are the good-prime and bad-prime extremes of the hypothesis
`HeckeCosetModule.mul_comm_of_antiInvolution` takes for commutativity of
`R(Γ₀(N), Δ₀(N))` (Shimura, Proposition 3.8); a mixed determinant needs both arguments at once.

A second criterion asks nothing of the determinant as a whole, only that the upper-left entry
of an integral witness be coprime to it. That one is entrywise; the bad-prime criterion is
recovered from it, since inside `Δ₀(N)` the upper-left entry is already a unit mod `N`.

An arbitrary determinant is then settled here, by a single argument that needs no case analysis:
a primitive witness of determinant `m` and its entry swap, which is primitive of the same
determinant, both lie in the double coset of `diag(1, m)`
(`mem_doubleCoset_natDiagGL_of_primitive`).
Passing from a primitive witness to a general one only costs a central scalar, which the bar
fixes. Running those two steps on an arbitrary `x ∈ Δ₀(N)` — divide an integral witness by the
gcd of its entries, then put the scalar back — leaves no double coset unfixed, so Shimura's
Proposition 3.8 applies: for nonzero level `N`, `R(Γ₀(N), Δ₀(N))` is commutative over any
commutative semiring.

## Main definitions

* `HeckeRing.GL2.atkinLehnerAntiInvolution`: the anti-involution of the `Γ₀(N)` Hecke pair.
* `HeckeRing.GL2.atkinLehnerAutomorphism`: the automorphism `g ↦ ι(g⁻¹)` of the ambient group.
* `HeckeRing.GL2.commSemiringHeckeRingGamma0`: for nonzero level `N`, the resulting
  commutative-semiring structure on the Hecke ring `R(Γ₀(N), Δ₀(N))`.

## Main results

* `HeckeRing.GL2.atkinLehnerAntiInvolution_bar`: how it acts, `g ↦ w · gᵀ · w⁻¹`. The bundle
  itself is opaque, so this is the elimination rule a consumer works with.
* `HeckeRing.GL2.atkinLehnerAntiInvolution_bar_val`: its entrywise action on a `Δ₀(N)` witness.
* `HeckeRing.GL2.atkinLehnerAntiInvolution_bar_det`: it preserves the determinant.
* `HeckeRing.GL2.atkinLehnerAntiInvolution_bar_mem_doubleCoset_of_coprimeDet`: it fixes the
  double coset when the determinant is coprime to the level.
* `HeckeRing.GL2.atkinLehnerAntiInvolution_bar_mem_doubleCoset_of_coprime_upperLeft`: it fixes
  the double coset when the upper-left entry of an integral witness is coprime to the
  determinant.
* `HeckeRing.GL2.atkinLehnerAntiInvolution_bar_mem_doubleCoset_of_dvd_pow`: it fixes the double
  coset when the determinant divides a power of the level, the witness-free specialisation of
  the previous one.
* `HeckeRing.GL2.atkinLehnerAntiInvolution_bar_mem_doubleCoset_of_smul`: the criterion survives
  scaling, the scalar's positivity and coprimality to the level being automatic.
* `HeckeRing.GL2.atkinLehnerAntiInvolution_bar_mem_doubleCoset_of_primitive`: it fixes the
  double coset of a witness no prime divides entrywise, with no hypothesis on the determinant.
* `HeckeRing.GL2.atkinLehnerAntiInvolution_bar_mem_doubleCoset`: for nonzero level `N`, it fixes
  the double coset of every `x ∈ Δ₀(N)`, with no further hypothesis on `x`.
* `HeckeRing.GL2.atkinLehnerAntiInvolution_onHeckeCoset_eq_self`: equivalently, for nonzero
  level `N`, it acts as the identity on `Γ₀(N) \ Δ₀(N) / Γ₀(N)`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Proposition 3.8.
* Ported from the AINTLIB `LeanModularForms` project (Chris Birkbeck),
  [`HeckeRIngs/GLn/CongruenceHecke/AtkinLehner.lean`](https://github.com/CBirkbeck/AINTLIB),
  declarations `wN`, `Gamma0_AL_hom`, `Gamma0_AL_involutive`, `Gamma0_AL_map_H`,
  `Gamma0_AL_map_Δ` and `Gamma0_antiInvolution`, and — for the results added here —
  `Gamma0_AL_bar_det`, `bar_eq_SL2_conj`, `Gamma0_AL_in_DC_coprime`, `Gamma0_AL_in_DC_bad`,
  `Gamma0_AL_in_DC_of_gcd_a00_m_coprime`, `Gamma0_AL_in_DC_of_smul`,
  `Gamma0_AL_in_DC_primitive`, `Gamma0_AL_in_doubleCoset`, `Gamma0_onHeckeCoset_eq` and
  `instCommRing_Gamma0`, all Apache-2.0 at commit
  `2baa76f742bdb4fb8ee323fabba41203bd390e08`. The source states its own transpose equivalence
  and diagonal-matrix API; here those come from `GLn/TransposeAntiInvolution.lean` and
  `GLn/DiagonalCosets.lean` instead, and the four-field bundle is assembled by
  `HeckeAntiInvolution.ofAmbient`. The source proves its own `Gamma0_AL_preserves_00` to see
  that the bar fixes the upper-left entry; here that is already visible in
  `atkinLehnerAntiInvolution_bar_val`, so the lemma is not reproduced. The source builds its
  central scalar by hand and proves centrality entrywise; here it is `natDiagGL` at a constant
  family, and centrality is read off `natDiagGL_const_comm`. The source's two reductions
  `Gamma0_AL_scalar_reduce` and `bar_mem_DC_of_bar_conj_mem` are used in the general form
  `HeckeRing.Commutativity` gives them, not re-proved for `Γ₀(N)`. The source builds the content
  quotient of a witness inline; here that is `exists_primitive_content_quotient`. Its
  `instCommRing_Gamma0` is a `CommRing` on the integral Hecke ring; the structure available
  here is the `CommSemiring` of `HeckeCosetModule.commSemiringOfAntiInvolution` over an
  arbitrary commutative semiring, exactly as at level one. The source's
  `Gamma0_pair_HeckeAlgebra_mul_comm` restates that instance's `mul_comm`, which
  `HeckeCosetModule.mul_comm_of_antiInvolution` already provides directly, so it is not
  reproduced.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup Subgroup HeckeRing.GLn

open scoped MatrixGroups HeckeCosetModule

namespace HeckeRing.GL2

variable (N : ℕ)

/-- `ι(g) = w · gᵀ · w⁻¹`, as a homomorphism to the opposite group. -/
private noncomputable def atkinLehnerHom : GL (Fin 2) ℚ →* (GL (Fin 2) ℚ)ᵐᵒᵖ where
  toFun g := MulOpposite.op (natDiagGL 2 ![1, N] *
    (transposeGLEquiv 2 g).unop * (natDiagGL 2 ![1, N])⁻¹)
  map_one' := by simp
  map_mul' a b := by
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_op, MulOpposite.unop_mul]
    have h1 : (transposeGLEquiv 2 (a * b)).unop =
        (transposeGLEquiv 2 b).unop * (transposeGLEquiv 2 a).unop := by
      simp only [map_mul, MulOpposite.unop_mul]
    rw [h1]; group

/-- **The value of `ι`**, stated once so the three consumers below and the public `bar`
lemma do not each rely on unfolding the definition. -/
@[simp] private lemma atkinLehnerHom_unop (g : GL (Fin 2) ℚ) :
    (atkinLehnerHom N g).unop =
      natDiagGL 2 ![1, N] * (transposeGLEquiv 2 g).unop * (natDiagGL 2 ![1, N])⁻¹ := (rfl)

/-- `ι` is involutive: transposition is, and the two conjugations by `w` cancel because
transposition fixes `w`. -/
private lemma atkinLehnerHom_involutive (g : GL (Fin 2) ℚ) :
    (atkinLehnerHom N (atkinLehnerHom N g).unop).unop = g := by
  simp only [atkinLehnerHom_unop]
  have h_tr : (transposeGLEquiv 2 (natDiagGL 2 ![1, N] *
      (transposeGLEquiv 2 g).unop * (natDiagGL 2 ![1, N])⁻¹)).unop =
      (transposeGLEquiv 2 (natDiagGL 2 ![1, N])⁻¹).unop *
        (transposeGLEquiv 2 (transposeGLEquiv 2 g).unop).unop *
        (transposeGLEquiv 2 (natDiagGL 2 ![1, N])).unop := by
    rw [map_mul, map_mul]
    simp only [MulOpposite.unop_mul]
    group
  have h_inv : (transposeGLEquiv 2 (natDiagGL 2 ![1, N])⁻¹).unop =
      (natDiagGL 2 ![1, N])⁻¹ := by
    rw [map_inv, MulOpposite.unop_inv, transposeGLEquiv_natDiagGL 2 ![1, N]]
  rw [h_tr, transposeGLEquiv_transposeGLEquiv, transposeGLEquiv_natDiagGL 2 ![1, N], h_inv]
  group

/-- The ambient Atkin–Lehner anti-involution as an equivalence with the opposite group. -/
private noncomputable def atkinLehnerEquiv : GL (Fin 2) ℚ ≃* (GL (Fin 2) ℚ)ᵐᵒᵖ where
  toFun := atkinLehnerHom N
  invFun g := (atkinLehnerHom N g.unop).unop
  left_inv := atkinLehnerHom_involutive N
  right_inv g := by
    apply MulOpposite.unop_injective
    exact atkinLehnerHom_involutive N g.unop
  map_mul' := map_mul (atkinLehnerHom N)

/-- The entries of `ι(g)`: `(a, b; N c, e) ↦ (a, c; N b, e)`, as an integral matrix. Gives the
value lemma, the determinant lemma and the two membership proofs one spelling instead of four
copies of the literal; the public `atkinLehnerAntiInvolution_bar_val` writes the matrix out
rather than exposing this constructor. -/
private def atkinLehnerEntries (A : Matrix (Fin 2) (Fin 2) ℤ) (c : ℤ) :
    Matrix (Fin 2) (Fin 2) ℤ :=
  !![A 0 0, c; (N : ℤ) * A 0 1, A 1 1]

/-- The integral matrix of `ι(g)`. Conjugating the transpose by `w = diag(1, N)` divides the
upper-right entry by `N` and multiplies the lower-left by `N`; the first is integral exactly
because `N ∣ A 1 0`, which is the `Δ₀(N)` shape. The two diagonal entries are untouched — in
particular the upper-left one, which is why every coprimality hypothesis about it survives.

This is the one computation both membership proofs below need, so it is done once here. -/
private lemma atkinLehnerHom_unop_val [NeZero N] (g : GL (Fin 2) ℚ)
    (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : (g : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (c : ℤ) (hc : A 1 0 = (N : ℤ) * c) :
    (((atkinLehnerHom N g).unop : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      (atkinLehnerEntries N A c).map (Int.cast : ℤ → ℚ) := by
  have hpos : ∀ i : Fin 2, 0 < (![1, N]) i := by
    intro i; fin_cases i <;> simp [NeZero.pos]
  have hNe : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hw : ((natDiagGL 2 ![1, N] : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      Matrix.diagonal ![1, (N : ℚ)] := by
    rw [natDiagGL_coe 2 _ hpos]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hwinv : (((natDiagGL 2 ![1, N])⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      Matrix.diagonal ![1, (N : ℚ)⁻¹] := by
    rw [Matrix.coe_units_inv, hw]
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hNe]
  have hcast : ((A 1 0 : ℤ) : ℚ) = (N : ℚ) * ((c : ℤ) : ℚ) := by
    exact_mod_cast congrArg (Int.cast : ℤ → ℚ) hc
  simp only [atkinLehnerHom_unop, atkinLehnerEntries, Units.val_mul, hw, hwinv,
    transposeGLEquiv_coe, hA]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.map_apply,
      Matrix.transpose_apply, hcast] <;>
    field_simp

/-- Conjugating the transpose by `w` swaps which off-diagonal entry carries the factor `N`, so
the determinant is unchanged. Both membership proofs need this, at different right-hand sides. -/
private lemma atkinLehnerEntries_det (A : Matrix (Fin 2) (Fin 2) ℤ) (c : ℤ)
    (hc : A 1 0 = (N : ℤ) * c) : (atkinLehnerEntries N A c).det = A.det := by
  rw [atkinLehnerEntries, Matrix.det_fin_two_of, Matrix.det_fin_two, hc]
  ring

/-- `ι` preserves the image of `Γ₀(N)`: the transported matrix again has determinant one and
lower-left entry divisible by `N`. -/
private lemma atkinLehnerHom_mem_Gamma0Image [NeZero N] (g : GL (Fin 2) ℚ)
    (hg : g ∈ Gamma0Image N) : (atkinLehnerHom N g).unop ∈ Gamma0Image N := by
  rw [mem_Gamma0Image_iff] at hg ⊢
  obtain ⟨σ, hσ_mem, rfl⟩ := hg
  rw [mem_Gamma0_iff_dvd] at hσ_mem
  obtain ⟨c, hc⟩ := hσ_mem
  set A := (σ : Matrix (Fin 2) (Fin 2) ℤ) with hA_def
  set B : Matrix (Fin 2) (Fin 2) ℤ := atkinLehnerEntries N A c with hB
  have hB_det : B.det = 1 := by rw [hB, atkinLehnerEntries_det N A c hc, hA_def, σ.2]
  refine ⟨⟨B, hB_det⟩, mem_Gamma0_iff_dvd.mpr ?_, Units.ext ?_⟩
  · simp only [hB, atkinLehnerEntries]
    exact dvd_mul_right _ _
  · -- the entrywise cast of an integral special-linear element, inlined as at
    -- `GL2/DiagonalCosetDegree.lean`
    have hval : ∀ μ : SpecialLinearGroup (Fin 2) ℤ,
        ((mapGL ℚ μ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
          (μ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ) :=
      fun μ ↦ by simp [mapGL_coe_matrix, algebraMap_int_eq, RingHom.mapMatrix_apply]
    rw [atkinLehnerHom_unop_val N _ A (hval σ) c hc, hval ⟨B, hB_det⟩]

/-- `ι` preserves `Δ₀(N)`: the determinant and the upper-left entry are unchanged, and the new
lower-left entry `N · A 0 1` is visibly divisible by `N`. -/
private lemma atkinLehnerHom_mem_Delta0 [NeZero N] (g : GL (Fin 2) ℚ) (hg : g ∈ Delta0 N) :
    (atkinLehnerHom N g).unop ∈ Delta0 N := by
  obtain ⟨A, hA, hdet, hAN, hAunit⟩ := (mem_Delta0_iff N).mp hg
  obtain ⟨c, hc⟩ := hAN
  set B : Matrix (Fin 2) (Fin 2) ℤ := atkinLehnerEntries N A c with hB
  have hval := atkinLehnerHom_unop_val N g A hA c hc
  have hB_det : B.det = A.det := by rw [hB, atkinLehnerEntries_det N A c hc]
  refine (mem_Delta0_iff N).mpr ⟨B, hval, ?_, ⟨A 0 1, by simp [hB, atkinLehnerEntries]⟩, ?_⟩
  · rw [hval, ← Int.cast_det, hB_det, Int.cast_det, ← hA]
    exact hdet
  · simpa [hB, atkinLehnerEntries] using hAunit

/-- **The Atkin-Lehner anti-involution** `g ↦ w · gᵀ · w⁻¹` of the `Γ₀(N)` Hecke pair, where
`w = diag(1, N)`.

`w` is the diagonal rescaling that repairs the transpose's failure to preserve `Γ₀(N)`. It is
**not** the Atkin-Lehner matrix of the operator `𝒲_Q`, which is `!![0, -1; N, 0]`.

Stated at the **unfolded** `(Gamma0 N).map (mapGL ℚ)`, which is where
`Gamma0/Basic.lean` puts the `IsHeckeTriple` instance. That matters and is not cosmetic:
`HeckeCosetModule.mul_comm_of_antiInvolution` asks for a `HeckeAntiInvolution Δ H` together
with `[IsHeckeTriple Δ H H]` at the *same* `H`, and instance search does not see through the
sealed `Gamma0Image` definition. Stated at `Gamma0Image N` the two do not compose at all —
the Hecke ring `𝕋 (Delta0 N) (Gamma0Image N) ℤ` does not even have a multiplication, since
that too comes from the instance. Measured both ways. -/
noncomputable def atkinLehnerAntiInvolution [NeZero N] :
    HeckeAntiInvolution (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) :=
  HeckeAntiInvolution.ofAmbient (atkinLehnerHom N) (atkinLehnerHom_involutive N)
    (fun g hg ↦ by
      rw [← Gamma0Image_def] at hg ⊢
      exact atkinLehnerHom_mem_Gamma0Image N g hg)
    (atkinLehnerHom_mem_Delta0 N)

/-- The automorphism of the ambient group sending `g` to the Atkin–Lehner bar of `g⁻¹`.

Composing two order reversals makes this multiplicative. It is the form of the Atkin–Lehner
operation used to transport left-coset multiplicities arising from right slash actions. -/
noncomputable def atkinLehnerAutomorphism : GL (Fin 2) ℚ ≃* GL (Fin 2) ℚ :=
  (MulEquiv.inv' (GL (Fin 2) ℚ)).trans (atkinLehnerEquiv N).symm

/-- The ambient automorphism is the Atkin–Lehner bar applied after inversion. -/
-- This is deliberately not a simp lemma: simp rewrites inner applications first, preventing
-- `atkinLehnerAutomorphism_involutive` from normalizing nested applications. Use `rw` when the
-- matrix entries are wanted.
lemma atkinLehnerAutomorphism_apply (x : GL (Fin 2) ℚ) :
    atkinLehnerAutomorphism N x = natDiagGL 2 ![1, N] *
      (transposeGLEquiv 2 x⁻¹).unop * (natDiagGL 2 ![1, N])⁻¹ :=
  (rfl)

/-- Coercing the ambient automorphism to a monoid hom does not change its value. -/
private lemma atkinLehnerAutomorphism_toMonoidHom_apply (x : GL (Fin 2) ℚ) :
    (atkinLehnerAutomorphism N : GL (Fin 2) ℚ →* GL (Fin 2) ℚ) x =
      atkinLehnerAutomorphism N x :=
  (rfl)

/-- The ambient Atkin–Lehner automorphism is involutive. -/
@[simp] lemma atkinLehnerAutomorphism_involutive (x : GL (Fin 2) ℚ) :
    atkinLehnerAutomorphism N (atkinLehnerAutomorphism N x) = x := by
  rw [atkinLehnerAutomorphism_apply, ← atkinLehnerHom_unop,
    atkinLehnerAutomorphism_apply, ← atkinLehnerHom_unop]
  rw [map_inv, MulOpposite.unop_inv, atkinLehnerHom_involutive, inv_inv]

/-- The ambient Atkin–Lehner automorphism is its own inverse. -/
@[simp] theorem atkinLehnerAutomorphism_symm :
    (atkinLehnerAutomorphism N).symm = atkinLehnerAutomorphism N :=
  MulEquiv.ext fun x ↦ (atkinLehnerAutomorphism N).injective <| by
    rw [(atkinLehnerAutomorphism N).apply_symm_apply, atkinLehnerAutomorphism_involutive]

/-- The ambient Atkin–Lehner automorphism preserves the image of `Γ₀(N)`. -/
@[simp] theorem atkinLehnerAutomorphism_map_Gamma0 [NeZero N] :
    ((Gamma0 N).map (mapGL ℚ)).map (atkinLehnerAutomorphism N :
        GL (Fin 2) ℚ →* GL (Fin 2) ℚ) = (Gamma0 N).map (mapGL ℚ) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [atkinLehnerAutomorphism_toMonoidHom_apply, atkinLehnerAutomorphism_apply,
      ← atkinLehnerHom_unop]
    rw [← Gamma0Image_def] at hy ⊢
    exact atkinLehnerHom_mem_Gamma0Image N y⁻¹ (inv_mem hy)
  · intro hx
    refine ⟨atkinLehnerAutomorphism N x, ?_, atkinLehnerAutomorphism_involutive N x⟩
    rw [atkinLehnerAutomorphism_apply, ← atkinLehnerHom_unop]
    rw [← Gamma0Image_def] at hx ⊢
    exact atkinLehnerHom_mem_Gamma0Image N x⁻¹ (inv_mem hx)

/-- The anti-involution acts by conjugating the transpose by `w`, unfolding the sealed
definition. -/
@[simp] lemma atkinLehnerAntiInvolution_bar [NeZero N] {x : GL (Fin 2) ℚ} (hx : x ∈ Delta0 N) :
    (atkinLehnerAntiInvolution N).bar x hx =
      natDiagGL 2 ![1, N] * (transposeGLEquiv 2 x).unop * (natDiagGL 2 ![1, N])⁻¹ :=
  HeckeAntiInvolution.ofAmbient_bar _ _ _ _ x hx

/-- On an inverse from `Δ₀(N)`, the ambient automorphism is the restricted Atkin–Lehner bar. -/
lemma atkinLehnerAutomorphism_inv_apply [NeZero N] {x : GL (Fin 2) ℚ}
    (hx : x ∈ Delta0 N) :
    atkinLehnerAutomorphism N x⁻¹ = (atkinLehnerAntiInvolution N).bar x hx := by
  rw [atkinLehnerAutomorphism_apply, inv_inv, atkinLehnerAntiInvolution_bar]

/-- **The entrywise action**, on the bundle: `(a, b; N c, e) ↦ (a, c; N b, e)`. This is the
form a consumer of `Δ₀(N)` elements needs; without it the entries can only be recovered by
redoing the diagonal-conjugation computation. -/
lemma atkinLehnerAntiInvolution_bar_val [NeZero N] {x : GL (Fin 2) ℚ} (hx : x ∈ Delta0 N)
    (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : (x : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (c : ℤ) (hc : A 1 0 = (N : ℤ) * c) :
    (((atkinLehnerAntiInvolution N).bar x hx : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      (!![A 0 0, c; (N : ℤ) * A 0 1, A 1 1]).map (Int.cast : ℤ → ℚ) := by
  have hbar : ((atkinLehnerAntiInvolution N).bar x hx : GL (Fin 2) ℚ) = (atkinLehnerHom N x).unop :=
    HeckeAntiInvolution.ofAmbient_bar _ _ _ _ x hx
  rw [hbar]
  exact atkinLehnerHom_unop_val N x A hA c hc

/-- The ambient map preserves determinants: conjugation cannot change one, and neither can
transposition. Stated for every `x : GL (Fin 2) ℚ`, since nothing here needs `Δ₀(N)`. -/
private lemma atkinLehnerHom_unop_det (x : GL (Fin 2) ℚ) :
    (((atkinLehnerHom N x).unop : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det =
      (x : Matrix (Fin 2) (Fin 2) ℚ).det := by
  simp only [atkinLehnerHom, MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_op,
    Units.val_mul, Matrix.det_units_conj, transposeGLEquiv_coe, Matrix.det_transpose]

/-- **The bar preserves the determinant**, so a determinant hypothesis on `x` transfers to
`bar x` unchanged. -/
-- Deliberately not `@[simp]`: `atkinLehnerAntiInvolution_bar` is already `@[simp]` and its
-- left-hand side `bar x hx` is a strict subterm of this one's, so `simp` unfolds the bar first
-- and this lemma's left-hand side is never in normal form. Tagging it makes `lint-env` fail with
-- one new `simpNF` violation; measured, not assumed. Do not add the annotation.
lemma atkinLehnerAntiInvolution_bar_det [NeZero N] {x : GL (Fin 2) ℚ}
    (hx : x ∈ Delta0 N) :
    (((atkinLehnerAntiInvolution N).bar x hx : GL (Fin 2) ℚ) :
        Matrix (Fin 2) (Fin 2) ℚ).det = (x : Matrix (Fin 2) (Fin 2) ℚ).det := by
  have hbar : ((atkinLehnerAntiInvolution N).bar x hx : GL (Fin 2) ℚ) =
      (atkinLehnerHom N x).unop :=
    HeckeAntiInvolution.ofAmbient_bar _ _ _ _ x hx
  rw [hbar]
  exact atkinLehnerHom_unop_det N x

/-- Common divisors of an integral matrix survive the entry swap defining the Atkin–Lehner
bar, provided they are coprime to the level. -/
private lemma dvd_atkinLehnerEntries (A : Matrix (Fin 2) (Fin 2) ℤ) (e c : ℤ)
    (hc : A 1 0 = (N : ℤ) * c) (he : ∀ i j, e ∣ A i j)
    (heN : IsCoprime e (N : ℤ)) :
    ∀ i j, e ∣ atkinLehnerEntries N A c i j := by
  intro i j
  fin_cases i <;> fin_cases j
  · simpa [atkinLehnerEntries] using he 0 0
  · simpa [atkinLehnerEntries] using heN.dvd_of_dvd_mul_left (hc ▸ he 1 0)
  · simpa [atkinLehnerEntries] using dvd_mul_of_dvd_right (he 0 1) (N : ℤ)
  · simpa [atkinLehnerEntries] using he 1 1

/-- The integral matrices of `x` and its Atkin–Lehner bar are equivalent under determinant-one
row and column operations. Smith normal form reduces this to preservation of the determinant
and of the content; the latter is where the `Δ₀(N)` upper-left coprimality is used. -/
private lemma exists_sl2_mul_mul_eq_atkinLehnerEntries
    (A : Matrix (Fin 2) (Fin 2) ℤ) (hA_det_pos : 0 < A.det) (c : ℤ)
    (hc : A 1 0 = (N : ℤ) * c) (hAco : Int.gcd (A 0 0) N = 1) :
    ∃ P Q : SpecialLinearGroup (Fin 2) ℤ,
      (P : Matrix (Fin 2) (Fin 2) ℤ) * A * (Q : Matrix (Fin 2) (Fin 2) ℤ) =
        atkinLehnerEntries N A c := by
  set B := atkinLehnerEntries N A c with hB
  have hAco' : IsCoprime (A 0 0) (N : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr hAco
  have hB00 : B 0 0 = A 0 0 := by simp [hB, atkinLehnerEntries]
  have hBc : B 1 0 = (N : ℤ) * A 0 1 := by simp [hB, atkinLehnerEntries]
  have hswap : atkinLehnerEntries N B (A 0 1) = A := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hB, atkinLehnerEntries, hc]
  -- a common divisor of either matrix divides the upper-left entry, so is coprime to `N`, and
  -- then survives the entry swap in either direction
  refine Matrix.exists_SL_mul_mul_eq_of_det_eq_of_dvd_iff hA_det_pos.ne'
    (atkinLehnerEntries_det N A c hc) fun e ↦ ⟨fun he ↦ dvd_atkinLehnerEntries N A e c hc he
      (hAco'.of_isCoprime_of_dvd_left (he 0 0)), fun he i j ↦ ?_⟩
  have h := dvd_atkinLehnerEntries N B e (A 0 1) hBc he
    (hAco'.of_isCoprime_of_dvd_left (hB00 ▸ he 0 0)) i j
  rwa [hswap] at h

/-- **The Atkin–Lehner involution fixes a coprime-determinant double coset.** If `x ∈ Δ₀(N)`
has determinant coprime to `N`, then its bar lies in the `Γ₀(N)`-double coset of `x`. -/
-- The Smith normal forms of an integral witness for `x` and its entry-swapped bar agree: their
-- first invariant factors agree because the upper-left entry is coprime to `N`, and their second
-- invariant factors then agree because the determinants do. Thus they define the same level-one
-- double coset. Shimura's Proposition 3.31, `toLevelOneCoset_injOn`, recovers equality of the
-- `Γ₀(N)`-double cosets from that equality.
theorem atkinLehnerAntiInvolution_bar_mem_doubleCoset_of_coprimeDet [NeZero N]
    (x : GL (Fin 2) ℚ) (hx : x ∈ Delta0 N) (hcop : CoprimeDet N ⟨x, hx⟩) :
    (atkinLehnerAntiInvolution N).bar x hx ∈
      DoubleCoset.doubleCoset x ((Gamma0 N).map (mapGL ℚ))
        ((Gamma0 N).map (mapGL ℚ)) := by
  obtain ⟨A, hA, hdet, hAN, hAunit⟩ := (mem_Delta0_iff N).mp hx
  obtain ⟨c, hc⟩ := hAN
  set a : Delta0 N := ⟨x, hx⟩
  set b : Delta0 N :=
    ⟨(atkinLehnerAntiInvolution N).bar x hx,
      (atkinLehnerAntiInvolution N).bar_mem_Δ x hx⟩
  set B := atkinLehnerEntries N A c with hB
  have hbar : ((b : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      B.map (Int.cast : ℤ → ℚ) := by
    simpa only [b, hB, atkinLehnerEntries] using
      atkinLehnerAntiInvolution_bar_val N hx A hA c hc
  have hA_det_pos : 0 < A.det := by
    rw [← Int.cast_pos (R := ℚ), Int.cast_det, ← hA]
    exact hdet
  have hAco : Int.gcd (A 0 0) N = 1 := Int.isUnit_intCast_iff_gcd_eq_one.mp hAunit
  obtain ⟨P, Q, hPQ⟩ :=
    exists_sl2_mul_mul_eq_atkinLehnerEntries N A hA_det_pos c hc hAco
  have hb_cop : CoprimeDet N b := by
    rw [coprimeDet_iff N hbar, hB, atkinLehnerEntries_det N A c hc]
    exact (coprimeDet_iff N hA).mp hcop
  have hlevel : toLevelOneCoset N
      (HeckeCoset.mk ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) a) =
      toLevelOneCoset N
        (HeckeCoset.mk ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) b) := by
    simp only [toLevelOneCoset_mk]
    symm
    apply HeckeCoset.mk_eq_mk_of_mem
    rw [Submonoid.coe_inclusion, Submonoid.coe_inclusion]
    exact mem_doubleCoset_SLnZ_of_intMatrix_eq 2 P Q x (b : GL (Fin 2) ℚ) A B hA hbar
      (hPQ.trans hB.symm)
  have ha_cop : HeckeCoset.mk ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) a ∈
      {D | CoprimeDetCoset N N D} := (coprimeDetCoset_self_mk N a).mpr hcop
  have hb_coset_cop :
      HeckeCoset.mk ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) b ∈
        {D | CoprimeDetCoset N N D} := (coprimeDetCoset_self_mk N b).mpr hb_cop
  have hcoset := toLevelOneCoset_injOn N ha_cop hb_coset_cop hlevel
  have hdc : DoubleCoset.doubleCoset x ((Gamma0 N).map (mapGL ℚ))
      ((Gamma0 N).map (mapGL ℚ)) =
      DoubleCoset.doubleCoset (b : GL (Fin 2) ℚ) ((Gamma0 N).map (mapGL ℚ))
        ((Gamma0 N).map (mapGL ℚ)) := by
    simpa only [a] using HeckeCoset.eq_iff.mp hcoset
  rw [hdc]
  exact DoubleCoset.mem_doubleCoset_self _ _ _

/-- **The Atkin–Lehner involution fixes a double coset whose upper-left entry is coprime to
the determinant.** If `x ∈ Δ₀(N)` has integral witness `A` and determinant `m`, and `A 0 0` is
coprime to `m`, then `bar x` lies in the `Γ₀(N)`-double coset of `x` itself.

Where the other two criteria read the determinant as a whole, this one reads a single
*entry*. Membership of `Δ₀(N)` already forces `A 0 0` to be a unit mod `N`; this asks
the same at `m`.

The bad-prime criterion below is its witness-free specialisation. -/
theorem atkinLehnerAntiInvolution_bar_mem_doubleCoset_of_coprime_upperLeft [NeZero N] (m : ℕ)
    (x : GL (Fin 2) ℚ) (hx : x ∈ Delta0 N) (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : (x : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (hdet : (x : Matrix (Fin 2) (Fin 2) ℚ).det = (m : ℚ)) (ham : Int.gcd (A 0 0) m = 1) :
    (atkinLehnerAntiInvolution N).bar x hx ∈
      DoubleCoset.doubleCoset x ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) := by
  obtain ⟨B, hB, -, hBN, -⟩ := (mem_Delta0_iff N).mp hx
  obtain ⟨c, hc⟩ : (N : ℤ) ∣ A 1 0 := by
    rwa [Matrix.map_injective (Int.cast_injective (α := ℚ)) (hB.symm.trans hA)] at hBN
  rw [DoubleCoset.doubleCoset_eq_of_mem
    (mem_doubleCoset_natDiagGL_of_intWitness N m x A hA ⟨c, hc⟩ hdet ham)]
  exact mem_doubleCoset_natDiagGL_of_intWitness N m _ !![A 0 0, c; (N : ℤ) * A 0 1, A 1 1]
    (atkinLehnerAntiInvolution_bar_val N hx A hA c hc) (by simp)
    ((atkinLehnerAntiInvolution_bar_det N hx).trans hdet) (by simpa using ham)

/-- **The Atkin–Lehner involution fixes a bad-prime double coset.** If `x ∈ Δ₀(N)` has
determinant `m` with `m ∣ N ^ k`, then `bar x` lies in the `Γ₀(N)`-double coset of `x` itself.

This is the *bad* case, where `m` shares its primes with the level; the coprime case is
separate. It supplies the bad-prime half of the fixing hypothesis that
`HeckeCosetModule.mul_comm_of_antiInvolution` requires, and is the statement to quote when no
integral witness is in hand. -/
theorem atkinLehnerAntiInvolution_bar_mem_doubleCoset_of_dvd_pow [NeZero N] (m k : ℕ)
    (hm_dvd : m ∣ N ^ k) (x : GL (Fin 2) ℚ) (hx : x ∈ Delta0 N)
    (hdet : (x : Matrix (Fin 2) (Fin 2) ℚ).det = (m : ℚ)) :
    (atkinLehnerAntiInvolution N).bar x hx ∈
      DoubleCoset.doubleCoset x ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) := by
  obtain ⟨A, hA, -, -, hAunit⟩ := (mem_Delta0_iff N).mp hx
  refine atkinLehnerAntiInvolution_bar_mem_doubleCoset_of_coprime_upperLeft N m x hx A hA hdet ?_
  have hmN : (m : ℤ) ∣ (N : ℤ) ^ k := by exact_mod_cast Int.natCast_dvd_natCast.mpr hm_dvd
  exact Int.isCoprime_iff_gcd_eq_one.mp
    ((Int.isCoprime_iff_gcd_eq_one.mpr
      (Int.isUnit_intCast_iff_gcd_eq_one.mp hAunit)).pow_right.of_isCoprime_of_dvd_right hmN)

/-- **A scalar relating two `Δ₀(N)` elements is positive and coprime to the level.** These are
exactly what `atkinLehnerAntiInvolution_bar_mem_doubleCoset_of_smul` asks of its scalar `d`
before it can form `diag(d, d)` in `Δ₀(N)`, and both come free from `x ∈ Δ₀(N)` — which is why
that theorem assumes neither. -/
private lemma pos_and_coprime_of_coe_eq_smul (d : ℕ) (x x₀ : GL (Fin 2) ℚ)
    (hx : x ∈ Delta0 N) (hx₀ : x₀ ∈ Delta0 N)
    (hsmul : (x : Matrix (Fin 2) (Fin 2) ℚ) = (d : ℚ) • (x₀ : Matrix (Fin 2) (Fin 2) ℚ)) :
    0 < d ∧ Nat.Coprime d N := by
  obtain ⟨A, hA, hxdet, -, hAunit⟩ := (mem_Delta0_iff N).mp hx
  obtain ⟨A₀, hA₀, -, -, -⟩ := (mem_Delta0_iff N).mp hx₀
  have hmat : A.map (Int.cast : ℤ → ℚ) = (d : ℚ) • A₀.map (Int.cast : ℤ → ℚ) := by
    rw [← hA, hsmul, hA₀]
  have hA00 : A 0 0 = (d : ℤ) * A₀ 0 0 := by
    have h := congrFun (congrFun hmat 0) 0
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at h
    exact_mod_cast h
  refine ⟨?_, ?_⟩
  -- `d = 0` would collapse `x` to the zero matrix, against `0 < det x`
  · rcases Nat.eq_zero_or_pos d with rfl | h
    · rw [hsmul] at hxdet
      simp at hxdet
    · exact h
  -- the upper-left entry of `x`'s witness is `d * A₀ 0 0`, and it is a unit mod `N`
  · rw [← ZMod.isUnit_iff_coprime]
    have hsplit : ((A 0 0 : ℤ) : ZMod N) = (d : ZMod N) * ((A₀ 0 0 : ℤ) : ZMod N) := by
      rw [hA00]
      push_cast
      ring
    rw [hsplit] at hAunit
    exact isUnit_of_mul_isUnit_left hAunit

/-- **The criterion survives scaling.** If `x` is the multiple `d • x₀` of an element of `Δ₀(N)`
whose double coset the bar fixes, then the bar fixes the double coset of `x` as well. Neither
positivity of `d` nor coprimality of `d` to `N` is assumed: both are consequences of `x` lying
in `Δ₀(N)`. -/
-- The scalar `d` is central in `GL₂(ℚ)`, and the bar fixes it: its integral witness is diagonal,
-- and the entry swap of `atkinLehnerAntiInvolution_bar_val` moves nothing on a diagonal matrix.
-- So this is `HeckeAntiInvolution.bar_mem_doubleCoset_self_mul_of_mem_centralizer` at that
-- scalar, a central element lying in every centralizer.
theorem atkinLehnerAntiInvolution_bar_mem_doubleCoset_of_smul [NeZero N] (d : ℕ)
    (x x₀ : GL (Fin 2) ℚ) (hx : x ∈ Delta0 N) (hx₀ : x₀ ∈ Delta0 N)
    (hsmul : (x : Matrix (Fin 2) (Fin 2) ℚ) = (d : ℚ) • (x₀ : Matrix (Fin 2) (Fin 2) ℚ))
    (hfix : (atkinLehnerAntiInvolution N).bar x₀ hx₀ ∈
      DoubleCoset.doubleCoset x₀ ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ))) :
    (atkinLehnerAntiInvolution N).bar x hx ∈
      DoubleCoset.doubleCoset x ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) := by
  obtain ⟨hd, hdN⟩ := pos_and_coprime_of_coe_eq_smul N d x x₀ hx hx₀ hsmul
  set s : GL (Fin 2) ℚ := natDiagGL 2 (fun _ ↦ d) with hs_def
  have hs : s ∈ Delta0 N := natDiagGL_mem_Delta0_of_coprime N _ fun _ ↦ hdN
  have hs_wit : (s : Matrix (Fin 2) (Fin 2) ℚ) =
      (Matrix.diagonal (fun _ ↦ (d : ℤ))).map (Int.cast : ℤ → ℚ) :=
    natDiagGL_coe_eq_map_intCast 2 _ fun _ ↦ hd
  have hs_central : s ∈ Subgroup.center (GL (Fin 2) ℚ) :=
    Subgroup.mem_center_iff.mpr fun g ↦ (natDiagGL_const_comm 2 d g).symm
  have hbar : (atkinLehnerAntiInvolution N).bar s hs = s := by
    apply Units.ext
    rw [atkinLehnerAntiInvolution_bar_val N hs _ hs_wit 0 (by simp), hs_wit]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  have hxeq : x = s * x₀ := by
    apply Units.ext
    rw [Units.val_mul, hsmul, hs_wit]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.smul_apply, Matrix.diagonal]
  subst hxeq
  exact (atkinLehnerAntiInvolution N).bar_mem_doubleCoset_self_mul_of_mem_centralizer hs hx₀
    (Subgroup.center_le_centralizer _ hs_central) hbar hfix

/-- **The Atkin-Lehner involution fixes the double coset of a primitive witness.** If `x ∈ Δ₀(N)`
has an integral witness `A` no prime divides entrywise, then `bar x` lies in the `Γ₀(N)`-double
coset of `x`. No hypothesis is placed on the determinant. -/
-- A primitive witness and its entry swap are both primitive of the same determinant `m`, so both
-- lie in the double coset of `diag(1, m)` (`mem_doubleCoset_natDiagGL_of_primitive`). No case
-- analysis on `m` is needed, and neither `..._of_coprimeDet` nor `..._of_dvd_pow` is a
-- dependency of this proof.
theorem atkinLehnerAntiInvolution_bar_mem_doubleCoset_of_primitive [NeZero N]
    (x : GL (Fin 2) ℚ) (hx : x ∈ Delta0 N) (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : (x : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (hprim : ∀ p : ℕ, p.Prime → ¬((p : ℤ) ∣ A 0 0 ∧ (p : ℤ) ∣ A 0 1 ∧ (p : ℤ) ∣ A 1 0 ∧
      (p : ℤ) ∣ A 1 1)) :
    (atkinLehnerAntiInvolution N).bar x hx ∈
      DoubleCoset.doubleCoset x ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) := by
  -- an element of `Δ₀(N)` has a unique integral witness, so the divisibility and upper-left
  -- unit conditions carried by membership are conditions on `A` itself
  obtain ⟨A₀, hA₀, hxdet, hAN, hAunit⟩ := (mem_Delta0_iff N).mp hx
  obtain rfl : A = A₀ := Matrix.map_injective Int.cast_injective (hA.symm.trans hA₀)
  have hAco : Int.gcd (A 0 0) N = 1 := Int.isUnit_intCast_iff_gcd_eq_one.mp hAunit
  have hA_det_pos : 0 < A.det := by rw [← Int.cast_pos (R := ℚ), Int.cast_det, ← hA]; exact hxdet
  obtain ⟨m, hm⟩ : ∃ m : ℕ, A.det = (m : ℤ) :=
    ⟨A.det.natAbs, (Int.natAbs_of_nonneg hA_det_pos.le).symm⟩
  have hdet_m : (x : Matrix (Fin 2) (Fin 2) ℚ).det = (m : ℚ) := by
    rw [hA, ← Int.cast_det A, hm]; norm_cast
  obtain ⟨c, hc⟩ := hAN
  rw [DoubleCoset.doubleCoset_eq_of_mem
    (mem_doubleCoset_natDiagGL_of_primitive N m x A hA ⟨c, hc⟩ hAco hdet_m hprim)]
  refine mem_doubleCoset_natDiagGL_of_primitive N m _ !![A 0 0, c; (N : ℤ) * A 0 1, A 1 1]
    (atkinLehnerAntiInvolution_bar_val N hx A hA c hc) (by simp) (by simpa using hAco)
    ((atkinLehnerAntiInvolution_bar_det N hx).trans hdet_m) ?_
  -- a prime dividing the swap entrywise divides `A 0 0`, so not `N`, and hence divides `A`
  rintro p hp ⟨h00, h01, h10, h11⟩
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one] at h00 h01 h10 h11
  have hpN : ¬(p : ℤ) ∣ N := fun hpN ↦ by
    have hu := (Int.isCoprime_iff_gcd_eq_one.mpr hAco).isUnit_of_dvd' h00 hpN
    have := hp.one_lt
    rcases Int.isUnit_iff.mp hu with h | h <;> omega
  refine hprim p hp ⟨h00, ?_, hc ▸ dvd_mul_of_dvd_right h01 _, h11⟩
  exact ((Nat.prime_iff_prime_int.mp hp).dvd_or_dvd h10).resolve_left hpN

/-- **The Atkin-Lehner bar fixes every `Γ₀(N)`-double coset in `Δ₀(N)`**, for nonzero level `N`
and with no further hypothesis on `x`. This is exactly the hypothesis Shimura's commutativity
criterion takes, in the pointwise form `HeckeAntiInvolution.bar_mem_doubleCoset_self` reads it.

Dividing an integral witness by the gcd `d` of its four entries leaves a primitive one, which
`atkinLehnerAntiInvolution_bar_mem_doubleCoset_of_primitive` settles with no hypothesis on the
determinant. Putting the scalar back is
`atkinLehnerAntiInvolution_bar_mem_doubleCoset_of_smul`, which asks nothing further of `d`: the
positivity and the coprimality to the level it needs are read off `x ∈ Δ₀(N)` inside it. -/
theorem atkinLehnerAntiInvolution_bar_mem_doubleCoset [NeZero N] (x : GL (Fin 2) ℚ)
    (hx : x ∈ Delta0 N) : (atkinLehnerAntiInvolution N).bar x hx ∈
      DoubleCoset.doubleCoset x ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) := by
  obtain ⟨A, hA, hxdet, hAN, hAunit⟩ := (mem_Delta0_iff N).mp hx
  have hAco : Int.gcd (A 0 0) N = 1 := Int.isUnit_intCast_iff_gcd_eq_one.mp hAunit
  have hA_det_pos : 0 < A.det := by
    rw [← Int.cast_pos (R := ℚ), Int.cast_det, ← hA]
    exact hxdet
  -- divide the witness by the gcd `d` of its four entries
  set d : ℕ := Nat.gcd (Nat.gcd (A 0 0).natAbs (A 0 1).natAbs)
    (Nat.gcd (A 1 0).natAbs (A 1 1).natAbs) with hd_def
  obtain ⟨A₀, hA₀_eq, hA₀_det_pos, hA₀N, hA₀co, hA₀_prim⟩ :=
    exists_primitive_content_quotient N A hA_det_pos hAN hAco d hd_def
  have hA₀_det_ne : (A₀.map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
    rw [← Int.cast_det]
    exact_mod_cast hA₀_det_pos.ne'
  set x₀ : GL (Fin 2) ℚ := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hA₀_det_ne
  have hx₀_val : (x₀ : Matrix (Fin 2) (Fin 2) ℚ) = A₀.map (Int.cast : ℤ → ℚ) := by simp [x₀]
  have hx₀_det : 0 < (x₀ : Matrix (Fin 2) (Fin 2) ℚ).det := by
    rw [hx₀_val, ← Int.cast_det]
    exact_mod_cast hA₀_det_pos
  have hx₀ : x₀ ∈ Delta0 N := (mem_Delta0_iff N).mpr ⟨A₀, hx₀_val, hx₀_det, hA₀N,
    Int.isUnit_intCast_iff_gcd_eq_one.mpr hA₀co⟩
  have hsmul : (x : Matrix (Fin 2) (Fin 2) ℚ) = (d : ℚ) • (x₀ : Matrix (Fin 2) (Fin 2) ℚ) := by
    rw [hA, hx₀_val]
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    exact_mod_cast congrArg (Int.cast : ℤ → ℚ) (hA₀_eq i j)
  exact atkinLehnerAntiInvolution_bar_mem_doubleCoset_of_smul N d x x₀ hx hx₀ hsmul
    (atkinLehnerAntiInvolution_bar_mem_doubleCoset_of_primitive N x₀ hx₀ A₀ hx₀_val hA₀_prim)

/-- **The Atkin-Lehner bar acts trivially on `Γ₀(N) \ Δ₀(N) / Γ₀(N)`**, for nonzero level `N`.
Each double coset is fixed, by `atkinLehnerAntiInvolution_bar_mem_doubleCoset` at any
representative. -/
@[simp] lemma atkinLehnerAntiInvolution_onHeckeCoset_eq_self [NeZero N]
    (D : HeckeCoset (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ))) :
    (atkinLehnerAntiInvolution N).onHeckeCoset D = D := by
  induction D using HeckeCoset.induction with
  | h g =>
    rw [(atkinLehnerAntiInvolution N).onHeckeCoset_mk]
    exact HeckeCoset.mk_eq_mk_of_mem
      (atkinLehnerAntiInvolution_bar_mem_doubleCoset N (g : GL (Fin 2) ℚ) g.2)

/-- **Shimura's Proposition 3.8 for `Γ₀(N)`**: for nonzero level `N`, the Hecke ring
`R(Γ₀(N), Δ₀(N))` over any commutative semiring is commutative, the Atkin-Lehner bar being an
anti-involution that fixes every double coset.

This is the level-`N` counterpart of `HeckeRing.GLn.commSemiringHeckeRing`, where transposition
alone does the same job. Not an instance, for the reason given there: the anti-involution is
data. The `@[instance_reducible]` attribute is required by Lean's class-definition
reducibility linter for any `def` of class type; it governs unfolding during instance search
and registers nothing on its own. -/
@[instance_reducible]
noncomputable def commSemiringHeckeRingGamma0 [NeZero N] (R : Type*) [CommSemiring R] :
    CommSemiring (𝕋 (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) R) :=
  HeckeCosetModule.commSemiringOfAntiInvolution R (atkinLehnerAntiInvolution N)
    (atkinLehnerAntiInvolution_onHeckeCoset_eq_self N)

end HeckeRing.GL2
