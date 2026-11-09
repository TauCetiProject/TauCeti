/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Decomposition
public import TauCeti.LinearAlgebra.FreeProduct.Star
public import TauCeti.LinearAlgebra.PiTensorProduct.Fin
import TauCeti.Algebra.Star.BigOperators
import Mathlib.Data.List.Chain
import Mathlib.Data.List.OfFn
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.RingTheory.TensorProduct.Maps
import TauCeti.Algebra.DirectSum.Internal

/-!
# Reduced-word linear decomposition of an algebraic free product

Given unital `R`-algebras `A i` over a commutative ring `R` and normalized `R`-linear functionals
`φ i : A i →ₗ[R] R` (`φ i 1 = 1`), each factor splits as `A i = R · 1 ⊕ ker (φ i)`. Multiplying
centered letters along alternating index sequences `w = [i₁, …, iₙ]` (`iₖ ≠ iₖ₊₁`) yields an
`R`-linear equivalence (`LinearAlgebra.FreeProduct.equivReducedWords`)

```text
FreeProduct R A ≃ₗ[R] ⨁ w : ReducedWord I, ⨂[R] k : Fin w.toList.length, ker (φ w.toList[k]),
```

where the empty word `ReducedWord.nil` corresponds to the scalar summand `R`. Equivalently, the
images `LinearAlgebra.FreeProduct.reducedWordSubmodule φ w` of the word-multiplication maps form an
internal direct-sum decomposition of `FreeProduct R A`
(`LinearAlgebra.FreeProduct.isInternal_reducedWordSubmodule`).

Instead of analysing confluence of word reductions directly, the proof constructs for each `i` the
splitting equivalence

```text
A i ⊗[R] (⨁ u : { w // w.toList.head? ≠ some i }, WordTensor φ u.1) ≃ₗ[R]
  ⨁ w : ReducedWord I, WordTensor φ w
```

(`LinearAlgebra.FreeProduct.factorTensorComplEquiv`), conjugates left multiplication on `A i` across
it to obtain a left `FreeProduct R A`-action on the reduced-word direct sum via the universal
property `LinearAlgebra.FreeProduct.lift`, and evaluates at the vacuum vector of the empty word.

## Main definitions

* `LinearAlgebra.FreeProduct.ReducedWord I` — alternating sequences of factor indices.
* `LinearAlgebra.FreeProduct.WordTensor φ w` and `LinearAlgebra.FreeProduct.wordMul φ w` — tensor
  products of centered subspaces `ker (φ wₖ)` and their ordered multiplication into
  `FreeProduct R A`.
* `LinearAlgebra.FreeProduct.reducedWordSubmodule φ w` — the `R`-submodule of `FreeProduct R A`
  spanned by centered alternating products of word `w`.
* `LinearAlgebra.FreeProduct.factorTensorComplEquiv φ hφi` — splitting of the reduced-word direct
  sum along a single factor `A i = R · 1 ⊕ ker (φ i)`.
* `LinearAlgebra.FreeProduct.equivReducedWords φ hφ` — the `R`-linear equivalence between
  `FreeProduct R A` and `⨁ w : ReducedWord I, WordTensor φ w`.

## Main results

* `LinearAlgebra.FreeProduct.isInternal_reducedWordSubmodule` — internal direct-sum decomposition of
  `FreeProduct R A` into `reducedWordSubmodule φ w`.
* `LinearAlgebra.FreeProduct.ι_injective_of_apply_one_eq_one` and
  `LinearAlgebra.FreeProduct.ι_injective` — injectivity of the canonical factor maps whenever
  normalized functionals exist, and unconditionally for nontrivial algebras over a field.
* `LinearAlgebra.FreeProduct.star_mem_reducedWordSubmodule` — compatibility of the reduced-word
  submodules with the star involution.

## References

* B. L. van der Waerden, *Free products of groups*, Amer. J. Math. **70** (1948).
* D. V. Voiculescu, K. J. Dykema, A. Nica, *Free Random Variables*, §§1.1–1.2, 1.4.
* D. Avitzour, *Free products of C*-algebras*, Trans. Amer. Math. Soc. **271** (1982), 423–435.

The splitting-and-left-action argument (`factorTensorComplEquiv`, `factorEndAlgHom`,
`leftActionAlgHom`, `toReducedWords`) is a linear analogue of the van der Waerden trick as
formalized for monoid coproducts in Mathlib's `Monoid.CoprodI.Word.equivPair` and
`Monoid.CoprodI.Word.summandAction` (`Mathlib.GroupTheory.CoprodI`). It builds on Mathlib's
`LinearAlgebra.FreeProduct.lift` and `Module.Projective.exists_dual_eq_one`, as well as
`LinearAlgebra.FreeProduct.ιStar` and `TauCeti.DirectSum.isInternal_of_lof`.
-/

public section

open scoped DirectSum TensorProduct

namespace LinearAlgebra.FreeProduct

/-! ### Reduced words of factor indices -/

/-- An alternating word of factor indices in `I`: a list in which consecutive entries are distinct.
The empty word indexes the scalar summand of `FreeProduct R A`. -/
@[ext]
structure ReducedWord (I : Type*) where
  /-- The underlying sequence of factor indices. -/
  toList : List I
  /-- Consecutive indices in the word are distinct. -/
  isChain : toList.IsChain (· ≠ ·)
  deriving DecidableEq

namespace ReducedWord

variable {I : Type*}

/-- The empty reduced word, indexing the scalar summand `R`. -/
abbrev nil : ReducedWord I := ⟨[], List.isChain_nil⟩

instance : Inhabited (ReducedWord I) := ⟨.nil⟩

@[simp]
theorem toList_nil : (nil : ReducedWord I).toList = [] := (rfl)

@[simp]
theorem toList_eq_nil_iff {w : ReducedWord I} : w.toList = [] ↔ w = .nil :=
  ⟨fun h ↦ ReducedWord.ext h, fun h ↦ by simp [h]⟩

/-- A single-letter reduced word `[i]`. -/
abbrev singleton (i : I) : ReducedWord I := ⟨[i], List.isChain_singleton _⟩

@[simp]
theorem toList_singleton (i : I) : (singleton i).toList = [i] := (rfl)

/-- A single-letter reduced word is nonempty. -/
theorem singleton_ne_nil (i : I) : singleton i ≠ .nil :=
  fun h ↦ List.cons_ne_nil i [] (congrArg toList h)

/-- The empty reduced word is distinct from any single-letter reduced word. -/
theorem nil_ne_singleton (i : I) : (.nil : ReducedWord I) ≠ singleton i :=
  (singleton_ne_nil i).symm

/-- Prepending an index `i` to a reduced word `w` whose initial index is not `i`. -/
abbrev cons {i : I} (w : ReducedWord I) (hw : w.toList.head? ≠ some i) : ReducedWord I :=
  ⟨i :: w.toList,
    List.isChain_cons.2 ⟨fun _j hj hij ↦ hw (hij ▸ Option.mem_def.1 hj), w.isChain⟩⟩

@[simp]
theorem toList_cons {i : I} (w : ReducedWord I) (hw : w.toList.head? ≠ some i) :
    (w.cons hw).toList = i :: w.toList :=
  (rfl)

/-- Prepending an index produces a nonempty reduced word. -/
theorem cons_ne_nil {i : I} (w : ReducedWord I) (hw : w.toList.head? ≠ some i) :
    w.cons hw ≠ .nil :=
  fun h ↦ List.cons_ne_nil i w.toList (congrArg toList h)

@[simp]
theorem cons_nil (i : I) : (.nil : ReducedWord I).cons (i := i) nofun = singleton i :=
  (rfl)

/-- Reversing a reduced word yields a reduced word, indexing the adjoint summand in star free
products. -/
abbrev reverse (w : ReducedWord I) : ReducedWord I :=
  ⟨w.toList.reverse, List.isChain_reverse.2 (w.isChain.imp fun _ _ h ↦ h.symm)⟩

@[simp]
theorem toList_reverse (w : ReducedWord I) : w.reverse.toList = w.toList.reverse :=
  (rfl)

@[simp]
theorem reverse_nil : (.nil : ReducedWord I).reverse = .nil :=
  (rfl)

@[simp]
theorem reverse_singleton (i : I) : (singleton i).reverse = singleton i :=
  (rfl)

@[simp]
theorem reverse_reverse (w : ReducedWord I) : w.reverse.reverse = w :=
  ReducedWord.ext w.toList.reverse_reverse

/-- Reversing reduced words is injective. -/
theorem reverse_injective : Function.Injective (reverse : ReducedWord I → ReducedWord I) :=
  Function.Involutive.injective reverse_reverse

/-- Reversing a reduced word gives `.nil` if and only if the word is `.nil`. -/
theorem reverse_eq_nil_iff {w : ReducedWord I} : w.reverse = .nil ↔ w = .nil :=
  ⟨fun h ↦ reverse_injective (by simpa using h), fun h ↦ by simp [h]⟩

/-- Structural induction on a `ReducedWord I` built from `.nil` and `ReducedWord.cons`. -/
@[elab_as_elim]
theorem cons_induction_on {motive : ReducedWord I → Prop} (w : ReducedWord I)
    (nil : motive .nil)
    (cons : ∀ {i : I} (u : ReducedWord I) (hu : u.toList.head? ≠ some i),
      motive u → motive (u.cons hu)) : motive w := by
  obtain ⟨l, hl⟩ := w
  induction l with
  | nil => exact nil
  | cons i rest ih =>
    exact cons ⟨rest, hl.tail⟩
      (fun h ↦ (List.isChain_cons.1 hl).1 i (Option.mem_def.2 h) rfl) (ih hl.tail)

end ReducedWord

/-! ### Tensor products of centered subspaces along reduced words -/

section WordTensor

variable {I : Type*} {R : Type*} [CommSemiring R]
  {A : I → Type*} [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)]

/-- The centered subspace `ker (φ wₖ)` at position `k` of a reduced word `w`. -/
abbrev WordTensorFactor (φ : ∀ i, A i →ₗ[R] R) (w : ReducedWord I)
    (k : Fin w.toList.length) : Type _ :=
  LinearMap.ker (φ w.toList[k])

/-- The tensor product `ker (φ i₁) ⊗[R] ⋯ ⊗[R] ker (φ iₙ)` of the centered subspaces along a
reduced word `w = [i₁, …, iₙ]`. For `w = .nil` this is the empty tensor product, isomorphic to
`R`. -/
abbrev WordTensor (φ : ∀ i, A i →ₗ[R] R) (w : ReducedWord I) : Type _ :=
  ⨂[R] k : Fin w.toList.length, WordTensorFactor φ w k

/-- The empty-word tensor product is canonically isomorphic to the base semiring `R`. -/
noncomputable def wordTensorNilEquiv (φ : ∀ i, A i →ₗ[R] R) :
    WordTensor φ (.nil : ReducedWord I) ≃ₗ[R] R :=
  PiTensorProduct.isEmptyEquiv (Fin 0)

@[simp↓]
theorem wordTensorNilEquiv_tprod (φ : ∀ i, A i →ₗ[R] R)
    (m : ∀ k, WordTensorFactor φ (.nil : ReducedWord I) k) :
    wordTensorNilEquiv φ (PiTensorProduct.tprod R m) = 1 :=
  PiTensorProduct.isEmptyEquiv_apply_tprod (Fin 0) m

/-- Under `wordTensorNilEquiv`, `1 : R` corresponds to the empty pure tensor. -/
theorem wordTensorNilEquiv_symm_one (φ : ∀ i, A i →ₗ[R] R) :
    (wordTensorNilEquiv φ).symm 1 =
      PiTensorProduct.tprod R (s := WordTensorFactor φ (.nil : ReducedWord I))
        (fun k ↦ k.elim0) :=
  (wordTensorNilEquiv φ).injective <| by
    rw [LinearEquiv.apply_symm_apply, wordTensorNilEquiv_tprod]

/-- A single-letter word tensor is canonically isomorphic to `ker (φ i)`. -/
noncomputable def wordTensorSingletonEquiv (φ : ∀ i, A i →ₗ[R] R) (i : I) :
    WordTensor φ (.singleton i) ≃ₗ[R] LinearMap.ker (φ i) :=
  PiTensorProduct.subsingletonEquiv (0 : Fin 1)

@[simp↓]
theorem wordTensorSingletonEquiv_tprod (φ : ∀ i, A i →ₗ[R] R) (i : I)
    (m : ∀ k, WordTensorFactor φ (.singleton i) k) :
    wordTensorSingletonEquiv φ i (PiTensorProduct.tprod R m) = m 0 :=
  PiTensorProduct.subsingletonEquiv_apply_tprod (0 : Fin 1) m

/-- Under `wordTensorSingletonEquiv`, an element `x ∈ ker (φ i)` corresponds to the one-factor
pure tensor with entry `x`. -/
theorem wordTensorSingletonEquiv_symm_apply (φ : ∀ i, A i →ₗ[R] R) (i : I)
    (x : LinearMap.ker (φ i)) :
    (wordTensorSingletonEquiv φ i).symm x =
      PiTensorProduct.tprod R
        (Fin.cons (α := WordTensorFactor φ (.singleton i)) x (fun k ↦ k.elim0)) :=
  (wordTensorSingletonEquiv φ i).injective <| by
    rw [LinearEquiv.apply_symm_apply, wordTensorSingletonEquiv_tprod]
    -- `WordTensorFactor φ (.singleton i) 0` unfolds `[i][0]` (`List.getElem`) to `i`.
    exact (Fin.cons_zero (α := WordTensorFactor φ (.singleton i)) x (fun k ↦ k.elim0)).symm

/-- Prepending a leading centered factor in `ker (φ i)` to `WordTensor φ w` gives
`WordTensor φ (w.cons hw)`. -/
noncomputable def wordTensorConsEquiv (φ : ∀ i, A i →ₗ[R] R) {i : I} (w : ReducedWord I)
    (hw : w.toList.head? ≠ some i) :
    LinearMap.ker (φ i) ⊗[R] WordTensor φ w ≃ₗ[R] WordTensor φ (w.cons hw) :=
  PiTensorProduct.finConsEquiv R (WordTensorFactor φ (w.cons hw))

@[simp]
theorem wordTensorConsEquiv_tmul (φ : ∀ i, A i →ₗ[R] R) {i : I} (w : ReducedWord I)
    (hw : w.toList.head? ≠ some i) (x : LinearMap.ker (φ i))
    (m : ∀ k, WordTensorFactor φ w k) :
    wordTensorConsEquiv φ w hw (x ⊗ₜ[R] PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R (Fin.cons (α := WordTensorFactor φ (w.cons hw)) x m) :=
  PiTensorProduct.finConsEquiv_tmul R (WordTensorFactor φ (w.cons hw)) x m

@[simp↓]
theorem wordTensorConsEquiv_symm_tprod (φ : ∀ i, A i →ₗ[R] R) {i : I} (w : ReducedWord I)
    (hw : w.toList.head? ≠ some i) (m : ∀ k, WordTensorFactor φ (w.cons hw) k) :
    (wordTensorConsEquiv φ w hw).symm (PiTensorProduct.tprod R m) =
      m 0 ⊗ₜ[R] PiTensorProduct.tprod R (Fin.tail m) :=
  PiTensorProduct.finConsEquiv_symm_tprod R (WordTensorFactor φ (w.cons hw)) m

section DecidableEq

variable [DecidableEq I]

/-- Ordered multiplication of centered tensor factors into `FreeProduct R A` along a reduced word
`w`. -/
noncomputable def wordMul (φ : ∀ i, A i →ₗ[R] R) (w : ReducedWord I) :
    WordTensor φ w →ₗ[R] FreeProduct R A :=
  PiTensorProduct.lift <|
    (MultilinearMap.mkPiAlgebraFin R w.toList.length (FreeProduct R A)).compLinearMap fun k ↦
      (ι R A w.toList[k]).toLinearMap.comp (LinearMap.ker (φ w.toList[k])).subtype

@[simp]
theorem wordMul_tprod (φ : ∀ i, A i →ₗ[R] R) (w : ReducedWord I)
    (m : ∀ k, WordTensorFactor φ w k) :
    wordMul φ w (PiTensorProduct.tprod R m) =
      (List.ofFn fun k ↦ ι R A w.toList[k] (m k)).prod :=
  PiTensorProduct.lift.tprod _

@[simp]
theorem wordMul_nil (φ : ∀ i, A i →ₗ[R] R) (z : WordTensor φ .nil) :
    wordMul φ .nil z = algebraMap R (FreeProduct R A) (wordTensorNilEquiv φ z) := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    rw [map_smul, map_smul, wordMul_tprod, wordTensorNilEquiv_tprod]
    simp [Algebra.algebraMap_eq_smul_one]
  | add x y hx hy =>
    simp [map_add, hx, hy]

@[simp]
theorem wordMul_singleton (φ : ∀ i, A i →ₗ[R] R) (i : I) (z : WordTensor φ (.singleton i)) :
    wordMul φ (.singleton i) z = ι R A i (wordTensorSingletonEquiv φ i z) := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    simp only [map_smul, SetLike.val_smul]
    rw [wordMul_tprod, wordTensorSingletonEquiv_tprod, List.ofFn_succ]
    simp only [List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
    -- `m 0` has dependent type `LinearMap.ker (φ [i][0])`, so `[i][0] = i` cannot be rewritten
    -- propositionally without casting `m 0`; `List.getElem` reduces `[i][0]` to `i` definitionally.
    rfl
  | add x y hx hy =>
    simp [map_add, hx, hy]

@[simp]
theorem wordMul_wordTensorConsEquiv_tmul (φ : ∀ i, A i →ₗ[R] R) {i : I} (w : ReducedWord I)
    (hw : w.toList.head? ≠ some i) (x : LinearMap.ker (φ i)) (z : WordTensor φ w) :
    wordMul φ (w.cons hw) (wordTensorConsEquiv φ w hw (x ⊗ₜ[R] z)) =
      ι R A i x * wordMul φ w z := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    simp only [TensorProduct.tmul_smul, map_smul, Algebra.mul_smul_comm,
      wordTensorConsEquiv_tmul]
    rw [wordMul_tprod, wordMul_tprod, List.ofFn_succ, List.prod_cons]
    -- `(w.cons hw).toList` is `i :: w.toList`, whose `List.getElem` at `0` and `k.succ` reduces
    -- definitionally to `i` and `w.toList[k]`, aligning the dependent fiber `WordTensorFactor` so
    -- `Fin.cons_zero` and `Fin.cons_succ` rewrite the head and tail factors.
    change r • (ι R A i (Fin.cons (α := WordTensorFactor φ (w.cons hw)) x m 0).1 *
        (List.ofFn fun k : Fin w.toList.length ↦
          ι R A w.toList[k]
            (Fin.cons (α := WordTensorFactor φ (w.cons hw)) x m k.succ).1).prod) =
      r • (ι R A i x * (List.ofFn fun k ↦ ι R A w.toList[k] (m k)).prod)
    rw [Fin.cons_zero (α := WordTensorFactor φ (w.cons hw)) x m]
    have htail :
        (List.ofFn fun k : Fin w.toList.length ↦
          ι R A w.toList[k]
            (Fin.cons (α := WordTensorFactor φ (w.cons hw)) x m k.succ).1) =
        List.ofFn fun k ↦ ι R A w.toList[k] (m k) :=
      congrArg List.ofFn (funext fun k ↦ by
        rw [Fin.cons_succ (α := WordTensorFactor φ (w.cons hw)) x m k])
    rw [htail]
  | add y₁ y₂ hy₁ hy₂ =>
    simp [TensorProduct.tmul_add, map_add, mul_add, hy₁, hy₂]

/-- The `R`-linear map assembling all reduced-word tensor summands into `FreeProduct R A`. Over a
commutative ring with normalized functionals `φ i 1 = 1`, this is the inverse of
`equivReducedWords`. -/
noncomputable def reducedWordsToFreeProduct (φ : ∀ i, A i →ₗ[R] R) :
    (⨁ w : ReducedWord I, WordTensor φ w) →ₗ[R] FreeProduct R A :=
  DirectSum.toModule R (ReducedWord I) (FreeProduct R A) (wordMul φ)

@[simp]
theorem reducedWordsToFreeProduct_lof (φ : ∀ i, A i →ₗ[R] R) (w : ReducedWord I)
    (z : WordTensor φ w) :
    reducedWordsToFreeProduct φ (DirectSum.lof R (ReducedWord I) (WordTensor φ) w z) =
      wordMul φ w z :=
  DirectSum.toModule_lof R w z

/-- The `R`-submodule of `FreeProduct R A` spanned by products of centered letters with reduced
index sequence `w`. -/
noncomputable def reducedWordSubmodule (φ : ∀ i, A i →ₗ[R] R) (w : ReducedWord I) :
    Submodule R (FreeProduct R A) :=
  LinearMap.range (wordMul φ w)

/-- An element belongs to `reducedWordSubmodule φ w` if and only if it lies in the range of
`wordMul φ w`. -/
theorem mem_reducedWordSubmodule {φ : ∀ i, A i →ₗ[R] R} {w : ReducedWord I}
    {x : FreeProduct R A} :
    x ∈ reducedWordSubmodule φ w ↔ ∃ z : WordTensor φ w, wordMul φ w z = x :=
  LinearMap.mem_range

/-- Every image of `wordMul φ w` lies in `reducedWordSubmodule φ w`. -/
theorem wordMul_mem_reducedWordSubmodule (φ : ∀ i, A i →ₗ[R] R) (w : ReducedWord I)
    (z : WordTensor φ w) : wordMul φ w z ∈ reducedWordSubmodule φ w :=
  LinearMap.mem_range_self _ z

/-- Any alternating product of `φ`-centered factor elements belongs to the corresponding
`reducedWordSubmodule`. -/
theorem list_prod_mem_reducedWordSubmodule (φ : ∀ i, A i →ₗ[R] R) (l : List (Σ i, A i))
    (halt : (l.map Sigma.fst).IsChain (· ≠ ·))
    (hker : ∀ x ∈ l, x.2 ∈ LinearMap.ker (φ x.1)) :
    (l.map fun x ↦ ι R A x.1 x.2).prod ∈ reducedWordSubmodule φ ⟨l.map Sigma.fst, halt⟩ := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.prod_nil]
    refine ⟨(wordTensorNilEquiv φ).symm 1, ?_⟩
    rw [wordMul_nil, LinearEquiv.apply_symm_apply, map_one]
  | cons hd tl ih =>
    obtain ⟨z, hz⟩ := ih halt.tail fun x hx ↦ hker x (List.mem_cons_of_mem _ hx)
    simp only [List.map_cons, List.prod_cons, ← hz]
    exact ⟨_, wordMul_wordTensorConsEquiv_tmul φ ⟨tl.map Sigma.fst, halt.tail⟩
      (fun h ↦ (List.isChain_cons.1 halt).1 hd.1 (Option.mem_def.2 h) rfl)
      ⟨hd.2, hker hd List.mem_cons_self⟩ z⟩

end DecidableEq

end WordTensor

/-! ### Splitting by normalized functionals and the reduced-word equivalence -/

section Ring

variable {I : Type*} {R : Type*} [CommRing R]
  {A : I → Type*} [∀ i, Ring (A i)] [∀ i, Algebra R (A i)]

/-- Centering an element of `A i` with respect to a normalized functional `φ i`:
`a ↦ a - algebraMap R (A i) (φ i a)`. -/
def centerLinearMap (φ : ∀ i, A i →ₗ[R] R) {i : I} (hφi : φ i 1 = 1) :
    A i →ₗ[R] LinearMap.ker (φ i) :=
  (LinearMap.id - (Algebra.linearMap R (A i)).comp (φ i)).codRestrict (LinearMap.ker (φ i))
    fun a ↦ by simp [Algebra.algebraMap_eq_smul_one, hφi]

@[simp]
theorem coe_centerLinearMap (φ : ∀ i, A i →ₗ[R] R) {i : I} (hφi : φ i 1 = 1) (a : A i) :
    (centerLinearMap φ hφi a : A i) = a - algebraMap R (A i) (φ i a) :=
  (rfl)

@[simp]
theorem centerLinearMap_algebraMap (φ : ∀ i, A i →ₗ[R] R) {i : I} (hφi : φ i 1 = 1) (r : R) :
    centerLinearMap φ hφi (algebraMap R (A i) r) = 0 := by
  ext
  simp [Algebra.algebraMap_eq_smul_one, hφi]

@[simp]
theorem centerLinearMap_one (φ : ∀ i, A i →ₗ[R] R) {i : I} (hφi : φ i 1 = 1) :
    centerLinearMap φ hφi 1 = 0 := by
  simpa using centerLinearMap_algebraMap φ hφi 1

@[simp]
theorem centerLinearMap_of_mem_ker (φ : ∀ i, A i →ₗ[R] R) {i : I} (hφi : φ i 1 = 1)
    {a : A i} (ha : a ∈ LinearMap.ker (φ i)) :
    centerLinearMap φ hφi a = ⟨a, ha⟩ := by
  ext
  simp [LinearMap.mem_ker.1 ha]

section Decomposition

variable [DecidableEq I]

private noncomputable def complInclusion (φ : ∀ i, A i →ₗ[R] R) (i : I) :
    (⨁ u : { w : ReducedWord I // w.toList.head? ≠ some i }, WordTensor φ u.1) →ₗ[R]
      ⨁ w : ReducedWord I, WordTensor φ w :=
  DirectSum.toModule R _ _ fun u ↦ DirectSum.lof R (ReducedWord I) (WordTensor φ) u.1

private noncomputable def consFromKer (φ : ∀ i, A i →ₗ[R] R) (i : I) :
    LinearMap.ker (φ i) ⊗[R]
        (⨁ u : { w : ReducedWord I // w.toList.head? ≠ some i }, WordTensor φ u.1) →ₗ[R]
      ⨁ w : ReducedWord I, WordTensor φ w :=
  TensorProduct.lift
    { toFun x := DirectSum.toModule R _ _ fun u ↦
        (DirectSum.lof R (ReducedWord I) (WordTensor φ) (u.1.cons u.2)).comp
          ((wordTensorConsEquiv φ u.1 u.2).toLinearMap.comp
            (TensorProduct.mk R _ _ x))
      map_add' x₁ x₂ := by
        apply DirectSum.linearMap_ext R
        intro u
        apply LinearMap.ext
        intro z
        simp
      map_smul' r x := by
        apply DirectSum.linearMap_ext R
        intro u
        apply LinearMap.ext
        intro z
        simp only [LinearMap.comp_apply, DirectSum.toModule_lof, TensorProduct.mk_apply,
          LinearMap.smul_apply, RingHom.id_apply, LinearEquiv.coe_coe]
        rw [TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul, map_smul] }

private noncomputable def factorTensorComplFwd (φ : ∀ i, A i →ₗ[R] R) {i : I}
    (hφi : φ i 1 = 1) :
    A i ⊗[R] (⨁ u : { w : ReducedWord I // w.toList.head? ≠ some i }, WordTensor φ u.1) →ₗ[R]
      ⨁ w : ReducedWord I, WordTensor φ w :=
  (TensorProduct.lid R _).toLinearMap.comp (TensorProduct.map (φ i) (complInclusion φ i)) +
    (consFromKer φ i).comp (TensorProduct.map (centerLinearMap φ hφi) LinearMap.id)

private noncomputable def bwdConsAux (φ : ∀ k, A k →ₗ[R] R) (i j : I) (rest : List I)
    (hl : (j :: rest).IsChain (· ≠ ·)) (hji : j = i) :
    WordTensor φ ⟨j :: rest, hl⟩ →ₗ[R]
      A i ⊗[R] ⨁ u : { w : ReducedWord I // w.toList.head? ≠ some i }, WordTensor φ u.1 := by
  cases hji
  have hrest : (⟨rest, hl.tail⟩ : ReducedWord I).toList.head? ≠ some i := by
    intro h
    exact (List.isChain_cons.1 hl).1 i (Option.mem_def.2 h) rfl
  exact (TensorProduct.map (LinearMap.ker (φ i)).subtype
    (DirectSum.lof R _ (fun u : { w : ReducedWord I // w.toList.head? ≠ some i } ↦ WordTensor φ u.1)
      ⟨⟨rest, hl.tail⟩, hrest⟩)).comp (wordTensorConsEquiv φ ⟨rest, hl.tail⟩ hrest).symm.toLinearMap

private noncomputable def bwdComponent (φ : ∀ k, A k →ₗ[R] R) (i : I) :
    ∀ w : ReducedWord I,
      WordTensor φ w →ₗ[R]
        A i ⊗[R] ⨁ u : { w : ReducedWord I // w.toList.head? ≠ some i }, WordTensor φ u.1
  | ⟨[], hl⟩ =>
    (TensorProduct.mk R (A i) _ 1).comp
      (DirectSum.lof R _
        (fun u : { w : ReducedWord I // w.toList.head? ≠ some i } ↦ WordTensor φ u.1)
        ⟨⟨[], hl⟩, nofun⟩)
  | ⟨j :: rest, hl⟩ =>
    if hji : j = i then
      bwdConsAux φ i j rest hl hji
    else
      (TensorProduct.mk R (A i) _ 1).comp
        (DirectSum.lof R _
          (fun u : { w : ReducedWord I // w.toList.head? ≠ some i } ↦ WordTensor φ u.1)
          ⟨⟨j :: rest, hl⟩, by simp [hji]⟩)

private noncomputable def factorTensorComplBwd (φ : ∀ k, A k →ₗ[R] R) (i : I) :
    (⨁ w : ReducedWord I, WordTensor φ w) →ₗ[R]
      A i ⊗[R] ⨁ u : { w : ReducedWord I // w.toList.head? ≠ some i }, WordTensor φ u.1 :=
  DirectSum.toModule R (ReducedWord I) _ (bwdComponent φ i)

private theorem bwdComponent_of_head_ne (φ : ∀ k, A k →ₗ[R] R) (i : I)
    (w : ReducedWord I) (hw : w.toList.head? ≠ some i) (z : WordTensor φ w) :
    bwdComponent φ i w z =
      1 ⊗ₜ[R] DirectSum.lof R _
        (fun v : { w : ReducedWord I // w.toList.head? ≠ some i } ↦ WordTensor φ v.1)
        ⟨w, hw⟩ z := by
  obtain ⟨_ | ⟨j, rest⟩, hl⟩ := w
  · simp [bwdComponent]
  · have hji : j ≠ i := fun h ↦ hw (by simp [h])
    simp [bwdComponent, hji]

private theorem bwdComponent_cons (φ : ∀ k, A k →ₗ[R] R) (i : I)
    (w : ReducedWord I) (hw : w.toList.head? ≠ some i) (x : LinearMap.ker (φ i))
    (z : WordTensor φ w) :
    bwdComponent φ i (w.cons hw) (wordTensorConsEquiv φ w hw (x ⊗ₜ[R] z)) =
      (x : A i) ⊗ₜ[R] DirectSum.lof R _
        (fun v : { w : ReducedWord I // w.toList.head? ≠ some i } ↦ WordTensor φ v.1)
        ⟨w, hw⟩ z := by
  obtain ⟨rest, hl⟩ := w
  simp [bwdComponent, bwdConsAux]

private theorem factorTensorComplBwd_lof_of_head_ne (φ : ∀ k, A k →ₗ[R] R) (i : I)
    (w : ReducedWord I) (hw : w.toList.head? ≠ some i) (z : WordTensor φ w) :
    factorTensorComplBwd φ i (DirectSum.lof R (ReducedWord I) (WordTensor φ) w z) =
      1 ⊗ₜ[R] DirectSum.lof R _
        (fun v : { w : ReducedWord I // w.toList.head? ≠ some i } ↦ WordTensor φ v.1)
        ⟨w, hw⟩ z :=
  (DirectSum.toModule_lof R w z).trans (bwdComponent_of_head_ne φ i w hw z)

@[simp]
private theorem factorTensorComplBwd_lof_cons (φ : ∀ k, A k →ₗ[R] R) (i : I)
    (w : ReducedWord I) (hw : w.toList.head? ≠ some i) (x : LinearMap.ker (φ i))
    (z : WordTensor φ w) :
    factorTensorComplBwd φ i
        (DirectSum.lof R (ReducedWord I) (WordTensor φ) (w.cons hw)
          (wordTensorConsEquiv φ w hw (x ⊗ₜ[R] z))) =
      (x : A i) ⊗ₜ[R] DirectSum.lof R _
        (fun v : { w : ReducedWord I // w.toList.head? ≠ some i } ↦ WordTensor φ v.1)
        ⟨w, hw⟩ z :=
  (DirectSum.toModule_lof R (w.cons hw) _).trans (bwdComponent_cons φ i w hw x z)

private theorem factorTensorComplFwd_comp_bwd (φ : ∀ k, A k →ₗ[R] R) {i : I}
    (hφi : φ i 1 = 1) :
    (factorTensorComplFwd φ hφi).comp (factorTensorComplBwd φ i) = LinearMap.id := by
  apply DirectSum.linearMap_ext R
  intro w
  apply LinearMap.ext
  intro z
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  induction w using ReducedWord.cons_induction_on with
  | nil =>
    simp [factorTensorComplBwd_lof_of_head_ne φ i .nil nofun, factorTensorComplFwd,
      complInclusion, consFromKer, hφi]
  | @cons j u hu _ =>
    by_cases hji : j = i
    · subst hji
      rw [← (wordTensorConsEquiv φ u hu).apply_symm_apply z]
      generalize (wordTensorConsEquiv φ u hu).symm z = t
      induction t using TensorProduct.inductionOn with
      | tmul x y =>
        simp [factorTensorComplFwd, complInclusion, consFromKer]
      | add s t hs ht => simp [map_add, hs, ht]
    · simp [factorTensorComplBwd_lof_of_head_ne φ i (u.cons hu) (by simp [hji]),
        factorTensorComplFwd, complInclusion, consFromKer, hφi]

private theorem factorTensorComplBwd_comp_fwd (φ : ∀ k, A k →ₗ[R] R) {i : I}
    (hφi : φ i 1 = 1) :
    (factorTensorComplBwd φ i).comp (factorTensorComplFwd φ hφi) = LinearMap.id := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply DirectSum.linearMap_ext R
  intro u
  apply LinearMap.ext
  intro z
  simp [factorTensorComplFwd, complInclusion, consFromKer,
    factorTensorComplBwd_lof_of_head_ne φ i u.1 u.2, ← TensorProduct.tmul_smul,
    ← TensorProduct.smul_tmul, ← TensorProduct.add_tmul, ← Algebra.algebraMap_eq_smul_one]

/-- Splitting `A i = R · 1 ⊕ ker (φ i)` identifies the tensor product of `A i` with reduced words
not starting with `i` with the full direct sum of reduced-word tensors. -/
noncomputable def factorTensorComplEquiv (φ : ∀ k, A k →ₗ[R] R) {i : I} (hφi : φ i 1 = 1) :
    A i ⊗[R] (⨁ u : { w : ReducedWord I // w.toList.head? ≠ some i }, WordTensor φ u.1) ≃ₗ[R]
      ⨁ w : ReducedWord I, WordTensor φ w :=
  LinearEquiv.ofLinearMap
    (factorTensorComplFwd φ hφi)
    (factorTensorComplBwd φ i)
    (factorTensorComplFwd_comp_bwd φ hφi)
    (factorTensorComplBwd_comp_fwd φ hφi)

@[simp]
theorem factorTensorComplEquiv_tmul_lof (φ : ∀ k, A k →ₗ[R] R) {i : I} (hφi : φ i 1 = 1)
    (a : A i) (u : { w : ReducedWord I // w.toList.head? ≠ some i }) (z : WordTensor φ u.1) :
    factorTensorComplEquiv φ hφi
        (a ⊗ₜ[R] DirectSum.lof R _
          (fun v : { w : ReducedWord I // w.toList.head? ≠ some i } ↦ WordTensor φ v.1) u z) =
      φ i a • DirectSum.lof R (ReducedWord I) (WordTensor φ) u.1 z +
        DirectSum.lof R (ReducedWord I) (WordTensor φ) (u.1.cons u.2)
          (wordTensorConsEquiv φ u.1 u.2 (centerLinearMap φ hφi a ⊗ₜ[R] z)) := by
  simp [factorTensorComplEquiv, factorTensorComplFwd, complInclusion, consFromKer]

/-- Evaluating `(factorTensorComplEquiv φ hφi).symm` on a reduced-word summand whose initial index
is not `i` places `1` in the `A i` factor. -/
theorem factorTensorComplEquiv_symm_lof_of_head_ne (φ : ∀ k, A k →ₗ[R] R) {i : I}
    (hφi : φ i 1 = 1) (w : ReducedWord I) (hw : w.toList.head? ≠ some i)
    (z : WordTensor φ w) :
    (factorTensorComplEquiv φ hφi).symm
        (DirectSum.lof R (ReducedWord I) (WordTensor φ) w z) =
      1 ⊗ₜ[R] DirectSum.lof R _
        (fun v : { w : ReducedWord I // w.toList.head? ≠ some i } ↦ WordTensor φ v.1)
        ⟨w, hw⟩ z :=
  factorTensorComplBwd_lof_of_head_ne φ i w hw z

/-- Evaluating `(factorTensorComplEquiv φ hφi).symm` on a reduced-word summand `w.cons hw` starting
with `i` splits off the leading centered factor in `A i`. -/
@[simp]
theorem factorTensorComplEquiv_symm_lof_cons (φ : ∀ k, A k →ₗ[R] R) {i : I}
    (hφi : φ i 1 = 1) (w : ReducedWord I) (hw : w.toList.head? ≠ some i)
    (x : LinearMap.ker (φ i)) (z : WordTensor φ w) :
    (factorTensorComplEquiv φ hφi).symm
        (DirectSum.lof R (ReducedWord I) (WordTensor φ) (w.cons hw)
          (wordTensorConsEquiv φ w hw (x ⊗ₜ[R] z))) =
      (x : A i) ⊗ₜ[R] DirectSum.lof R _
        (fun v : { w : ReducedWord I // w.toList.head? ≠ some i } ↦ WordTensor φ v.1)
        ⟨w, hw⟩ z :=
  factorTensorComplBwd_lof_cons φ i w hw x z

private theorem reducedWordsToFreeProduct_factorTensorComplEquiv (φ : ∀ k, A k →ₗ[R] R) {i : I}
    (hφi : φ i 1 = 1) (a : A i)
    (y : ⨁ u : { w : ReducedWord I // w.toList.head? ≠ some i }, WordTensor φ u.1) :
    reducedWordsToFreeProduct φ (factorTensorComplEquiv φ hφi (a ⊗ₜ[R] y)) =
      ι R A i a * reducedWordsToFreeProduct φ (complInclusion φ i y) := by
  induction y using DirectSum.induction_on with
  | zero => simp
  | of u z =>
    rw [← DirectSum.lof_eq_of R, factorTensorComplEquiv_tmul_lof]
    simp [complInclusion, sub_mul, Algebra.smul_def]
  | add y₁ y₂ hy₁ hy₂ => simp [TensorProduct.tmul_add, map_add, mul_add, hy₁, hy₂]

private noncomputable def factorEndAlgHom (φ : ∀ k, A k →ₗ[R] R) {i : I} (hφi : φ i 1 = 1) :
    A i →ₐ[R] Module.End R (⨁ w : ReducedWord I, WordTensor φ w) :=
  (((factorTensorComplEquiv φ hφi).conjAlgEquiv R).toAlgHom.comp
    (Module.End.rTensorAlgHom R (A i) _)).comp (Algebra.lmul R (A i))

private theorem factorEndAlgHom_apply (φ : ∀ k, A k →ₗ[R] R) {i : I} (hφi : φ i 1 = 1)
    (a : A i) (v : ⨁ w : ReducedWord I, WordTensor φ w) :
    factorEndAlgHom φ hφi a v =
      factorTensorComplEquiv φ hφi
        ((Algebra.lmul R (A i) a).rTensor _ ((factorTensorComplEquiv φ hφi).symm v)) :=
  (rfl)

private noncomputable def leftActionAlgHom (φ : ∀ k, A k →ₗ[R] R) (hφ : ∀ i, φ i 1 = 1) :
    FreeProduct R A →ₐ[R] Module.End R (⨁ w : ReducedWord I, WordTensor φ w) :=
  lift R A fun {i} ↦ factorEndAlgHom φ (hφ i)

private theorem reducedWordsToFreeProduct_leftActionAlgHom (φ : ∀ k, A k →ₗ[R] R)
    (hφ : ∀ i, φ i 1 = 1) (u : FreeProduct R A)
    (v : ⨁ w : ReducedWord I, WordTensor φ w) :
    reducedWordsToFreeProduct φ (leftActionAlgHom φ hφ u v) =
      u * reducedWordsToFreeProduct φ v := by
  induction u using FreeProduct.induction_on generalizing v with
  | algebraMap r =>
    simp [← Algebra.smul_def]
  | ι i a =>
    rw [leftActionAlgHom, lift_ι_apply, ← (factorTensorComplEquiv φ (hφ i)).apply_symm_apply v]
    generalize (factorTensorComplEquiv φ (hφ i)).symm v = t
    induction t using TensorProduct.inductionOn with
    | tmul b y =>
      simp [factorEndAlgHom_apply, reducedWordsToFreeProduct_factorTensorComplEquiv, mul_assoc]
    | add s t hs ht =>
      simp [map_add, mul_add, hs, ht]
  | mul x y hx hy =>
    simp [hx, hy, mul_assoc]
  | add x y hx hy =>
    simp [map_add, add_mul, hx, hy]

private noncomputable def toReducedWords (φ : ∀ k, A k →ₗ[R] R) (hφ : ∀ i, φ i 1 = 1) :
    FreeProduct R A →ₗ[R] ⨁ w : ReducedWord I, WordTensor φ w where
  toFun u := leftActionAlgHom φ hφ u
    (DirectSum.lof R (ReducedWord I) (WordTensor φ) .nil ((wordTensorNilEquiv φ).symm 1))
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

private theorem toReducedWords_apply (φ : ∀ k, A k →ₗ[R] R) (hφ : ∀ i, φ i 1 = 1)
    (u : FreeProduct R A) :
    toReducedWords φ hφ u = leftActionAlgHom φ hφ u
      (DirectSum.lof R (ReducedWord I) (WordTensor φ) .nil ((wordTensorNilEquiv φ).symm 1)) :=
  (rfl)

private theorem toReducedWords_wordMul (φ : ∀ k, A k →ₗ[R] R) (hφ : ∀ i, φ i 1 = 1)
    (w : ReducedWord I) :
    ∀ z : WordTensor φ w,
      toReducedWords φ hφ (wordMul φ w z) =
        DirectSum.lof R (ReducedWord I) (WordTensor φ) w z := by
  induction w using ReducedWord.cons_induction_on with
  | nil =>
    intro z
    rw [wordMul_nil, toReducedWords_apply, AlgHom.commutes]
    simp [Algebra.algebraMap_eq_smul_one, ← map_smul]
  | @cons i u hu ih =>
    intro z
    rw [← (wordTensorConsEquiv φ u hu).apply_symm_apply z]
    generalize (wordTensorConsEquiv φ u hu).symm z = t
    induction t using TensorProduct.inductionOn with
    | tmul x y =>
      simp_rw [toReducedWords_apply] at ih
      rw [wordMul_wordTensorConsEquiv_tmul, toReducedWords_apply]
      simp only [map_mul, Module.End.mul_eq_comp, LinearMap.comp_apply, ih y]
      rw [leftActionAlgHom, lift_ι_apply]
      simp only [factorEndAlgHom_apply,
        factorTensorComplEquiv_symm_lof_of_head_ne φ (hφ i) u hu,
        LinearMap.rTensor_tmul, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', mul_one]
      rw [factorTensorComplEquiv_tmul_lof]
      simp
    | add s t hs ht =>
      simp [map_add, hs, ht]

/-- **Reduced-word linear decomposition of `FreeProduct R A`.** Given normalized `R`-linear
functionals `φ i : A i →ₗ[R] R` (`φ i 1 = 1`), `FreeProduct R A` is canonically `R`-linearly
equivalent to the direct sum of the centered tensor products `WordTensor φ w` over all reduced
words `w`, with `ReducedWord.nil` corresponding to the scalar summand `R`. -/
noncomputable def equivReducedWords (φ : ∀ k, A k →ₗ[R] R) (hφ : ∀ i, φ i 1 = 1) :
    FreeProduct R A ≃ₗ[R] ⨁ w : ReducedWord I, WordTensor φ w :=
  LinearEquiv.ofLinearMap
    (toReducedWords φ hφ)
    (reducedWordsToFreeProduct φ)
    (DirectSum.linearMap_ext R fun w ↦ LinearMap.ext fun z ↦ by
      simp only [LinearMap.comp_apply, LinearMap.id_apply, reducedWordsToFreeProduct_lof]
      exact toReducedWords_wordMul φ hφ w z)
    (LinearMap.ext fun u ↦ by
      simp [toReducedWords_apply, reducedWordsToFreeProduct_leftActionAlgHom])

@[simp]
theorem equivReducedWords_symm_toLinearMap (φ : ∀ k, A k →ₗ[R] R) (hφ : ∀ i, φ i 1 = 1) :
    (equivReducedWords φ hφ).symm.toLinearMap = reducedWordsToFreeProduct φ :=
  (rfl)

@[simp]
theorem equivReducedWords_symm_apply (φ : ∀ k, A k →ₗ[R] R) (hφ : ∀ i, φ i 1 = 1)
    (v : ⨁ w : ReducedWord I, WordTensor φ w) :
    (equivReducedWords φ hφ).symm v = reducedWordsToFreeProduct φ v :=
  (rfl)

@[simp]
theorem equivReducedWords_wordMul (φ : ∀ k, A k →ₗ[R] R) (hφ : ∀ i, φ i 1 = 1)
    (w : ReducedWord I) (z : WordTensor φ w) :
    equivReducedWords φ hφ (wordMul φ w z) =
      DirectSum.lof R (ReducedWord I) (WordTensor φ) w z := by
  rw [← LinearEquiv.eq_symm_apply, equivReducedWords_symm_apply, reducedWordsToFreeProduct_lof]

@[simp]
theorem equivReducedWords_algebraMap (φ : ∀ k, A k →ₗ[R] R) (hφ : ∀ i, φ i 1 = 1) (r : R) :
    equivReducedWords φ hφ (algebraMap R (FreeProduct R A) r) =
      DirectSum.lof R (ReducedWord I) (WordTensor φ) .nil ((wordTensorNilEquiv φ).symm r) := by
  rw [← LinearEquiv.eq_symm_apply, equivReducedWords_symm_apply, reducedWordsToFreeProduct_lof,
    wordMul_nil, LinearEquiv.apply_symm_apply]

@[simp]
theorem equivReducedWords_one (φ : ∀ k, A k →ₗ[R] R) (hφ : ∀ i, φ i 1 = 1) :
    equivReducedWords φ hφ 1 =
      DirectSum.lof R (ReducedWord I) (WordTensor φ) .nil ((wordTensorNilEquiv φ).symm 1) := by
  simpa using equivReducedWords_algebraMap φ hφ 1

/-- Under `equivReducedWords`, a centered element of `A i` maps into the single-letter summand
`ReducedWord.singleton i`. -/
theorem equivReducedWords_ι_of_mem_ker (φ : ∀ k, A k →ₗ[R] R) (hφ : ∀ i, φ i 1 = 1)
    {i : I} {a : A i} (ha : a ∈ LinearMap.ker (φ i)) :
    equivReducedWords φ hφ (ι R A i a) =
      DirectSum.lof R (ReducedWord I) (WordTensor φ) (.singleton i)
        ((wordTensorSingletonEquiv φ i).symm ⟨a, ha⟩) := by
  rw [← LinearEquiv.eq_symm_apply, equivReducedWords_symm_apply, reducedWordsToFreeProduct_lof,
    wordMul_singleton, LinearEquiv.apply_symm_apply]

/-- Decomposition of a factor element `ι R A i a` into its scalar `.nil` part `φ i a` and its
centered single-letter `.singleton i` part. -/
theorem equivReducedWords_ι (φ : ∀ k, A k →ₗ[R] R) (hφ : ∀ i, φ i 1 = 1) (i : I) (a : A i) :
    equivReducedWords φ hφ (ι R A i a) =
      DirectSum.lof R (ReducedWord I) (WordTensor φ) .nil
        ((wordTensorNilEquiv φ).symm (φ i a)) +
      DirectSum.lof R (ReducedWord I) (WordTensor φ) (.singleton i)
        ((wordTensorSingletonEquiv φ i).symm (centerLinearMap φ (hφ i) a)) := by
  have ha : ι R A i a =
      algebraMap R (FreeProduct R A) (φ i a) + ι R A i (centerLinearMap φ (hφ i) a) := by
    rw [coe_centerLinearMap, map_sub, AlgHom.commutes, add_sub_cancel]
  rw [ha, map_add, equivReducedWords_algebraMap,
    equivReducedWords_ι_of_mem_ker φ hφ (centerLinearMap φ (hφ i) a).2]

/-- Each reduced-word multiplication map `wordMul φ w` is injective when the functionals `φ i` are
normalized. -/
theorem wordMul_injective (φ : ∀ k, A k →ₗ[R] R) (hφ : ∀ i, φ i 1 = 1) (w : ReducedWord I) :
    Function.Injective (wordMul φ w) := by
  intro x y hxy
  have := congrArg (equivReducedWords φ hφ) hxy
  rw [equivReducedWords_wordMul, equivReducedWords_wordMul] at this
  exact DirectSum.of_injective w this

/-- The linear equivalence between the abstract reduced-word tensor product `WordTensor φ w` and
its image submodule `reducedWordSubmodule φ w` inside `FreeProduct R A`. -/
noncomputable def wordTensorEquivSubmodule (φ : ∀ k, A k →ₗ[R] R) (hφ : ∀ i, φ i 1 = 1)
    (w : ReducedWord I) :
    WordTensor φ w ≃ₗ[R] reducedWordSubmodule φ w :=
  LinearEquiv.ofInjective (wordMul φ w) (wordMul_injective φ hφ w)

@[simp]
theorem coe_wordTensorEquivSubmodule (φ : ∀ k, A k →ₗ[R] R) (hφ : ∀ i, φ i 1 = 1)
    (w : ReducedWord I) (z : WordTensor φ w) :
    (wordTensorEquivSubmodule φ hφ w z : FreeProduct R A) = wordMul φ w z :=
  (rfl)

/-- The submodules `reducedWordSubmodule φ w` form an internal direct-sum decomposition of
`FreeProduct R A`. -/
theorem isInternal_reducedWordSubmodule (φ : ∀ k, A k →ₗ[R] R) (hφ : ∀ i, φ i 1 = 1) :
    DirectSum.IsInternal (reducedWordSubmodule φ) :=
  TauCeti.DirectSum.isInternal_of_lof (wordTensorEquivSubmodule φ hφ)
    (equivReducedWords φ hφ).symm fun w z ↦ by
      rw [equivReducedWords_symm_apply, reducedWordsToFreeProduct_lof, coe_wordTensorEquivSubmodule]

/-! ### Injectivity of factor maps and nontriviality -/

/-- When each factor admits a normalized `R`-linear functional, `algebraMap R (FreeProduct R A)` is
injective. -/
theorem algebraMap_injective_of_apply_one_eq_one {φ : ∀ k, A k →ₗ[R] R}
    (hφ : ∀ i, φ i 1 = 1) :
    Function.Injective (algebraMap R (FreeProduct R A)) := by
  intro r s hrs
  have h := congrArg
    (DirectSum.component R (ReducedWord I) (WordTensor φ) .nil ∘ equivReducedWords φ hφ) hrs
  simpa [DirectSum.component.of] using h

/-- When `R` is nontrivial and each factor admits a normalized `R`-linear functional,
`FreeProduct R A` is nontrivial. -/
theorem nontrivial_of_apply_one_eq_one [Nontrivial R] {φ : ∀ k, A k →ₗ[R] R}
    (hφ : ∀ i, φ i 1 = 1) :
    Nontrivial (FreeProduct R A) :=
  (algebraMap_injective_of_apply_one_eq_one hφ).nontrivial

/-- **Injectivity of factor embeddings.** Whenever every factor admits a normalized `R`-linear
functional `φ j 1 = 1`, every canonical factor homomorphism `ι R A i` is injective. -/
theorem ι_injective_of_apply_one_eq_one {φ : ∀ k, A k →ₗ[R] R}
    (hφ : ∀ j, φ j 1 = 1) (i : I) :
    Function.Injective (ι R A i) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have h := congrArg (equivReducedWords φ hφ) ha
  rw [equivReducedWords_ι φ hφ i a, map_zero] at h
  have hnil : φ i a = 0 := by
    have h0 := congrArg (DirectSum.component R (ReducedWord I) (WordTensor φ) .nil) h
    simpa [DirectSum.component.of, ReducedWord.singleton_ne_nil i] using h0
  have hsing : centerLinearMap φ (hφ i) a = 0 := by
    have h1 := congrArg (DirectSum.component R (ReducedWord I) (WordTensor φ) (.singleton i)) h
    simpa [DirectSum.component.of, ReducedWord.nil_ne_singleton i] using h1
  have hsub : a - algebraMap R (A i) (φ i a) = 0 := congrArg Subtype.val hsing
  simpa [hnil] using hsub

end Decomposition

/-! ### Field corollaries -/

section Field

variable {K : Type*} [Field K] [DecidableEq I]
  (B : I → Type*) [∀ i, Ring (B i)] [∀ i, Algebra K (B i)] [∀ i, Nontrivial (B i)]

/-- Over a field `K`, every canonical factor map into the unital free product of nontrivial
`K`-algebras is injective. -/
theorem ι_injective (i : I) : Function.Injective (ι K B i) := by
  choose φ hφ using fun j ↦ Module.Projective.exists_dual_eq_one K (one_ne_zero (α := B j))
  exact ι_injective_of_apply_one_eq_one hφ i

/-- Over a field `K`, the unital free product of any family of nontrivial `K`-algebras (including
the empty family) is nontrivial. -/
theorem nontrivial : Nontrivial (FreeProduct K B) := by
  choose φ hφ using fun j ↦ Module.Projective.exists_dual_eq_one K (one_ne_zero (α := B j))
  exact nontrivial_of_apply_one_eq_one hφ

end Field

end Ring

/-! ### Compatibility with the star structure -/

section Star

variable {I : Type*} {R : Type*} [CommSemiring R]
  {A : I → Type*} [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)]
  [DecidableEq I] [StarRing R] [∀ i, StarRing (A i)] [∀ i, StarModule R (A i)]

/-- When each functional `φ i` commutes with `star`, the involution on `FreeProduct R A` carries
`reducedWordSubmodule φ w` into `reducedWordSubmodule φ w.reverse`. -/
theorem star_mem_reducedWordSubmodule {φ : ∀ i, A i →ₗ[R] R}
    (hstar : ∀ i (a : A i), φ i (star a) = star (φ i a)) {w : ReducedWord I}
    {x : FreeProduct R A} (hx : x ∈ reducedWordSubmodule φ w) :
    star x ∈ reducedWordSubmodule φ w.reverse := by
  obtain ⟨z, rfl⟩ := hx
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    rw [map_smul, star_smul, wordMul_tprod]
    refine Submodule.smul_mem _ (star r) ?_
    let l : List (Σ i, A i) :=
      (List.ofFn fun k : Fin w.toList.length ↦
        (⟨w.toList[k], star (m k : A _)⟩ : Σ i, A i)).reverse
    have hprod : star (List.ofFn fun k ↦ ι R A w.toList[k] (m k)).prod =
        (l.map fun u ↦ ι R A u.1 u.2).prod := by
      rw [TauCeti.star_list_prod]
      simp [l, List.map_reverse, List.map_ofFn, Function.comp_def]
    have hfst : l.map Sigma.fst = w.reverse.toList := by
      simp [l, List.map_reverse, List.map_ofFn, Function.comp_def, List.ofFn_getElem]
    have halt : (l.map Sigma.fst).IsChain (· ≠ ·) := hfst ▸ w.reverse.isChain
    have hker : ∀ u ∈ l, u.2 ∈ LinearMap.ker (φ u.1) := by
      intro u hu
      simp only [l, List.mem_reverse, List.mem_ofFn] at hu
      obtain ⟨k, rfl⟩ := hu
      simp [LinearMap.mem_ker, hstar]
    have hw : (⟨l.map Sigma.fst, halt⟩ : ReducedWord I) = w.reverse :=
      ReducedWord.ext hfst
    rw [hprod, ← hw]
    exact list_prod_mem_reducedWordSubmodule φ l halt hker
  | add x y hx hy =>
    rw [map_add, star_add]
    exact add_mem hx hy

end Star

end LinearAlgebra.FreeProduct
