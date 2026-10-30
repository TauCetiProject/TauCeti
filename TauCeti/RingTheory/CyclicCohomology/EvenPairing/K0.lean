/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.CartanMap.Basic
public import TauCeti.LinearAlgebra.Matrix.Idempotent
public import TauCeti.RingTheory.CyclicCohomology.EvenPairing.Invariance

/-!
# The even pairing of cyclic cohomology with algebraic `K₀`

Let `A` be a unital algebra over a field `R` of characteristic zero. Algebraic `K₀(A)` is the
Grothendieck group of finitely generated projective left `A`-modules, here the exact `K₀` of the
split exact category of such modules (see `TauCeti.finiteProjectiveModulesExactStructure`). This
file shows that Connes' even pairing `⟨[e], [φ]⟩ = (m!)⁻¹ (φ#Tr)(e, …, e)` of idempotent matrices
with cyclic cohomology classes of degree `2m` descends to a homomorphism

```text
K₀(A) → (HC²ᵐ(A; M) →ₗ[R] M).
```

A finitely generated projective module `P` is isomorphic to the module of row vectors fixed by an
idempotent matrix `e` (`Module.Finite.exists_linearEquiv_range_vecMulLinear`), and `[P]` pairs
through `e`. The choice of `e` does not matter: two idempotents presenting isomorphic modules are
algebraically equivalent, `e = x y` and `f = y x`
(`Matrix.nonempty_linearEquiv_range_vecMulLinear_iff`), and the even pairing is invariant under
algebraic equivalence. The last fact reduces to conjugation invariance of the pairing: after
replacing `x` by `e x f` and `y` by `f y e`, the block matrix `w = !![1 - e, x; y, 1 - f]`
satisfies `w² = 1` and conjugates `e ⊕ 0` to `0 ⊕ f`. Additivity on short exact sequences follows
from additivity of the pairing on block sums, since a short exact sequence of projective modules
splits.

## Main definitions

* `TauCeti.cyclicCohomology.evenPairingK0`: the even pairing on algebraic `K₀`.

## Main results

* `TauCeti.cyclicCohomology.evenPairing_matrixExtension_eq_of_mul_eq`: invariance of the even
  pairing of idempotent matrices under algebraic equivalence.
* `TauCeti.cyclicCohomology.evenPairing_matrixExtension_eq_of_linearEquiv`: idempotent matrices
  presenting isomorphic modules have the same even pairing.
* `TauCeti.cyclicCohomology.evenPairingK0_of`: the pairing of the class of a module presented by an
  idempotent matrix `e` is the even pairing of `e`.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §3.
* J.-L. Loday, *Cyclic Homology*, §8.3.
* J. Rosenberg, *Algebraic K-Theory and Its Applications*, §1.2.
-/

public section

noncomputable section

universe u

open CategoryTheory LinearMap

namespace TauCeti

namespace cyclicCohomology

section AlgebraicEquivalence

variable {R A M : Type*} [Field R] [CharZero R] [Ring A] [Algebra R A] [AddCommGroup M]
  [Module R M]

/-- The even pairing with the zero idempotent vanishes. -/
@[simp]
theorem evenPairing_zero (m : ℕ) :
    evenPairing (R := R) (M := M) (0 : A) .zero m = 0 := by
  ext φ
  rw [LinearMap.comp_apply, evenPairing_mk, LinearMap.zero_comp, LinearMap.zero_apply,
    MultilinearMap.map_coord_zero _ (0 : Fin (2 * m + 1)) rfl, smul_zero]

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Bordering an idempotent matrix by a zero block does not change its even pairing. -/
private theorem evenPairing_fromBlocks_zero_matrixExtension {e : Matrix ι ι A}
    (he : IsIdempotentElem e) (m : ℕ) (c : cyclicCohomology R A M (2 * m)) :
    evenPairing (Matrix.fromBlocks e 0 0 (0 : Matrix κ κ A)) (he.fromBlocks_zero₁₂_zero₂₁ .zero) m
        (matrixExtension M (ι ⊕ κ) (2 * m) c) =
      evenPairing e he m (matrixExtension M ι (2 * m) c) := by
  rw [evenPairing_fromBlocks_matrixExtension he .zero, evenPairing_zero, LinearMap.zero_apply,
    add_zero]

/-- **Invariance of the even pairing under algebraic equivalence.** If `e = x y` and `f = y x` for
idempotent matrices `e` and `f` and rectangular matrices `x` and `y`, then `e` and `f` have the
same even pairing with every cyclic cohomology class. -/
theorem evenPairing_matrixExtension_eq_of_mul_eq {e : Matrix ι ι A} {f : Matrix κ κ A}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f) {x : Matrix ι κ A} {y : Matrix κ ι A}
    (hxy : x * y = e) (hyx : y * x = f) (m : ℕ) (c : cyclicCohomology R A M (2 * m)) :
    evenPairing e he m (matrixExtension M ι (2 * m) c) =
      evenPairing f hf m (matrixExtension M κ (2 * m) c) := by
  subst hxy hyx
  -- Idempotence of `x y` and `y x`, as rewriting rules on left-associated alternating words.
  have h₁' : x * y * x * y = x * y := by rw [Matrix.mul_assoc (x * y), he.eq]
  have h₂' : y * x * y * x = y * x := by rw [Matrix.mul_assoc (y * x), hf.eq]
  -- The block matrix `w = !![1 - x y, x y x; y x y, 1 - y x]` is an involution conjugating
  -- `x y ⊕ 0` to `0 ⊕ y x`.
  set w := Matrix.fromBlocks (1 - x * y) (x * y * x) (y * x * y) (1 - y * x)
  have hww : w * w = 1 := by
    rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
    congr 1 <;> simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one,
      ← Matrix.mul_assoc, h₁', h₂'] <;> abel
  have hconj : w * Matrix.fromBlocks (x * y) 0 0 0 * w = Matrix.fromBlocks 0 0 0 (y * x) := by
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    congr 1 <;> simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, ← Matrix.mul_assoc, h₁', h₂'] <;> abel
  let u : (Matrix (ι ⊕ κ) (ι ⊕ κ) A)ˣ := ⟨w, w, hww, hww⟩
  have key : ∀ (g : Matrix (ι ⊕ κ) (ι ⊕ κ) A) (hg : IsIdempotentElem g),
      (u : Matrix (ι ⊕ κ) (ι ⊕ κ) A) * Matrix.fromBlocks (x * y) 0 0 0 *
        (↑u⁻¹ : Matrix (ι ⊕ κ) (ι ⊕ κ) A) = g →
        evenPairing (R := R) (M := M) g hg m =
          evenPairing _ (he.fromBlocks_zero₁₂_zero₂₁ .zero) m := by
    rintro _ _ rfl
    exact evenPairing_units_conj u _ _ m
  rw [← evenPairing_fromBlocks_zero_matrixExtension (κ := κ) he,
    ← key _ (IsIdempotentElem.zero.fromBlocks_zero₁₂_zero₂₁ hf) hconj,
    evenPairing_fromBlocks_matrixExtension .zero hf, evenPairing_zero, LinearMap.zero_apply,
    zero_add]

/-- **The even pairing only depends on the module presented by an idempotent.** If idempotent
matrices `e` and `f` have isomorphic ranges of right multiplication on row vectors, then they have
the same even pairing with every cyclic cohomology class. -/
theorem evenPairing_matrixExtension_eq_of_linearEquiv {e : Matrix ι ι A} {f : Matrix κ κ A}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (ψ : range e.vecMulLinear ≃ₗ[A] range f.vecMulLinear) (m : ℕ)
    (c : cyclicCohomology R A M (2 * m)) :
    evenPairing e he m (matrixExtension M ι (2 * m) c) =
      evenPairing f hf m (matrixExtension M κ (2 * m) c) := by
  obtain ⟨x, y, hxy, hyx⟩ := (Matrix.nonempty_linearEquiv_range_vecMulLinear_iff he hf).1 ⟨ψ⟩
  exact evenPairing_matrixExtension_eq_of_mul_eq he hf hxy hyx m c

end AlgebraicEquivalence

section K0

variable {R : Type*} {A : Type u} {M : Type*} [Field R] [CharZero R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M]

/-- The even pairing of a finitely generated projective module, computed through an idempotent
matrix presenting it. -/
private def modulePairing (P : Type*) [AddCommGroup P] [Module A P] [Module.Finite A P]
    [Module.Projective A P] (m : ℕ) : cyclicCohomology R A M (2 * m) →ₗ[R] M :=
  have h := Module.Finite.exists_linearEquiv_range_vecMulLinear A P
  evenPairing h.choose_spec.choose h.choose_spec.choose_spec.1 m ∘ₗ
    matrixExtension M (Fin h.choose) (2 * m)

private theorem modulePairing_eq {P : Type*} [AddCommGroup P] [Module A P] [Module.Finite A P]
    [Module.Projective A P] {ι : Type*} [Fintype ι] [DecidableEq ι] {e : Matrix ι ι A}
    (he : IsIdempotentElem e) (ψ : P ≃ₗ[A] range e.vecMulLinear) (m : ℕ) :
    modulePairing (R := R) (M := M) P m = evenPairing e he m ∘ₗ matrixExtension M ι (2 * m) := by
  have h := Module.Finite.exists_linearEquiv_range_vecMulLinear A P
  refine LinearMap.ext fun c ↦ ?_
  exact evenPairing_matrixExtension_eq_of_linearEquiv _ he
    (h.choose_spec.choose_spec.2.some.symm.trans ψ) m c

private theorem modulePairing_eq_add {P Q₁ Q₂ : Type*} [AddCommGroup P] [Module A P]
    [Module.Finite A P] [Module.Projective A P] [AddCommGroup Q₁] [Module A Q₁]
    [Module.Finite A Q₁] [Module.Projective A Q₁] [AddCommGroup Q₂] [Module A Q₂]
    [Module.Finite A Q₂] [Module.Projective A Q₂] (ψ : P ≃ₗ[A] Q₁ × Q₂) (m : ℕ) :
    modulePairing (R := R) (A := A) (M := M) P m =
      modulePairing (R := R) (M := M) Q₁ m + modulePairing (R := R) (M := M) Q₂ m := by
  obtain ⟨n₁, e₁, he₁, ⟨ψ₁⟩⟩ := Module.Finite.exists_linearEquiv_range_vecMulLinear A Q₁
  obtain ⟨n₂, e₂, he₂, ⟨ψ₂⟩⟩ := Module.Finite.exists_linearEquiv_range_vecMulLinear A Q₂
  rw [modulePairing_eq he₁ ψ₁, modulePairing_eq he₂ ψ₂,
    modulePairing_eq (he₁.fromBlocks_zero₁₂_zero₂₁ he₂)
      (ψ.trans ((ψ₁.prodCongr ψ₂).trans (Matrix.rangeVecMulLinearFromBlocksEquiv e₁ e₂).symm))]
  exact LinearMap.ext (evenPairing_fromBlocks_matrixExtension he₁ he₂ m)

variable (R A M) in
/-- **Connes' even pairing on algebraic `K₀`.** The even pairing of idempotent matrices with
cyclic cohomology classes of degree `2m` descends to the Grothendieck group `K₀(A)` of finitely
generated projective left `A`-modules: the class of a module presented by an idempotent matrix `e`
pairs as `e` does (`TauCeti.cyclicCohomology.evenPairingK0_of`). -/
def evenPairingK0 (m : ℕ) :
    ExactK0.{u} (finiteProjectiveModulesExactStructure A) →+
      (cyclicCohomology R A M (2 * m) →ₗ[R] M) :=
  ExactK0.lift
    { obj X := modulePairing X.obj m
      map_conflation S hS := by
        -- A conflation is a short exact sequence of modules, split since `S.X₃` is projective.
        have hS' := (finiteProjectiveModulesExactStructure_conflation_iff A S).1 hS
        have hexact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hS'.exact
        obtain ⟨l, hl⟩ := Module.projective_lifting_property (P := S.X₃.obj)
          (S.map (finiteProjectiveModules A).ι).g.hom LinearMap.id hS'.moduleCat_surjective_g
        exact modulePairing_eq_add (P := S.X₂.obj) (Q₁ := S.X₁.obj) (Q₂ := S.X₃.obj)
          (hexact.splitSurjectiveEquiv hS'.moduleCat_injective_f ⟨l, hl⟩).1 m }

/-- **Connes' formula on `K₀`.** If a finitely generated projective module `X` is isomorphic to the
module of row vectors fixed by an idempotent matrix `e`, then the even pairing of its class with a
cyclic cohomology class is the even pairing `(m!)⁻¹ (φ#Tr)(e, …, e)` of `e`. -/
theorem evenPairingK0_of (X : (finiteProjectiveModules A).FullSubcategory) {ι : Type*}
    [Fintype ι] [DecidableEq ι] {e : Matrix ι ι A} (he : IsIdempotentElem e)
    (ψ : X.obj ≃ₗ[A] range e.vecMulLinear) (m : ℕ) (c : cyclicCohomology R A M (2 * m)) :
    evenPairingK0 R A M m (ExactK0.of X) c =
      evenPairing e he m (matrixExtension M ι (2 * m) c) := by
  rw [evenPairingK0, ExactK0.lift_of]
  exact LinearMap.congr_fun (modulePairing_eq he ψ m) c

end K0

end cyclicCohomology

end TauCeti
