/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.BarDifferential
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Homotopy.Basic
public import TauCeti.LinearAlgebra.TensorCoalgebra.Cup

/-!
# Symmetry and transitivity of homotopies of A-infinity morphisms

Homotopy of morphisms of `A∞` algebras is an equivalence relation, even though the naive sum
`H₁ + H₂` of a `(F, G)`-coderivation `H₁` and a `(G, K)`-coderivation `H₂` fails the
`(F, K)`-coderivation rule by the cross terms `(H₁ ⊗ G - G ⊗ H₂) ∘ (τ' ⊗ 1) ∘ Δ`, and `-H₁` fails
the `(G, F)`-coderivation rule for the same reason.

Following Lefèvre-Hasegawa (Section 1.3.1.2), both cross-term obstructions are killed on the nose
by adding the bar commutator `b_B ∘ U - U ∘ b_A` of the degree-`(-2)` cup operator
`U = gradedCoderivCup (AA.grading.shift 1) 1 F H₁ H₂` from
`TauCeti.LinearAlgebra.TensorCoalgebra.Cup`:

* **Transitivity** (`TauCeti.AInfinityHom.Homotopy.trans`): for `h₁ : Homotopy f g` and
  `h₂ : Homotopy g k`, the map `H₁ + H₂ + (b_B ∘ U - U ∘ b_A)` has degree `-1`, satisfies the
  `(F, K)`-coderivation rule (`deconcatenation_comp_sub_comp_of_cup`), and still has bar
  commutator `F - K` since `b_B² = 0` and `b_A² = 0`.
* **Symmetry** (`TauCeti.AInfinityHom.Homotopy.symm`): for `h : Homotopy f g`, solving the
  fixed-point equation `H' = -H - (b_B ∘ cup(F, H, H') - cup(F, H, H') ∘ b_A)` recursively along
  the tensor-length filtration produces a `(G, F)`-homotopy `h.symm : Homotopy g f` whose composite
  `h.trans h.symm` is literally `Homotopy.refl f`.

Consequently `TauCeti.AInfinityHom.Homotopic` (`Nonempty (Homotopy f g)`) is an equivalence
relation compatible with composition of `A∞` morphisms on both sides.

## Main definitions

* `TauCeti.AInfinityHom.Homotopy.copy`: transport a homotopy along equalities of endpoints.
* `TauCeti.AInfinityHom.Homotopy.ofTaylor`: construct a homotopy from its suspended Taylor
  components.
* `TauCeti.AInfinityHom.Homotopy.trans`: vertical composition of homotopies `Homotopy f g` and
  `Homotopy g k`.
* `TauCeti.AInfinityHom.Homotopy.symm`: reversal of a homotopy `Homotopy f g` to `Homotopy g f`.
* `TauCeti.AInfinityHom.Homotopic`: the proposition that two `A∞` morphisms are homotopic.

## Main results

* `TauCeti.AInfinityHom.Homotopy.trans_symm`: `h.trans h.symm = Homotopy.refl f`.
* `TauCeti.AInfinityHom.Homotopy.linearHomotopy_trans` and
  `TauCeti.AInfinityHom.Homotopy.linearHomotopy_symm`: on arity one, `trans` and `symm` act as
  addition and negation of chain homotopies.
* `TauCeti.AInfinityHom.equivalence_homotopic`: `Homotopic` is an equivalence relation.
* `TauCeti.AInfinityHom.Homotopic.comp`: `Homotopic` is compatible with horizontal composition.

## References

* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, thèse de doctorat, Université Paris 7
  (2003), Section 1.3.1.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.7.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe uR uA uB uC

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing R]
  [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

namespace AInfinityHom

open ReducedTensorWords

variable {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B} {CC : AInfinityAlgebra R C}

namespace Homotopy

/-! ### Endpoint transport and construction from Taylor components -/

/-- Transport a homotopy along equalities of its source and target morphisms, keeping the same
underlying map of bar constructions. -/
def copy {f g f' g' : AInfinityHom AA BB} (h : Homotopy f g) (hf : f = f') (hg : g = g') :
    Homotopy f' g' where
  barHomotopy := h.barHomotopy
  isGradedCoderivationAlong_barHomotopy := by
    subst hf; subst hg; exact h.isGradedCoderivationAlong_barHomotopy
  isHomogeneous_barHomotopy := h.isHomogeneous_barHomotopy
  barMap_sub_barMap := by
    subst hf; subst hg; exact h.barMap_sub_barMap

/-- Transporting a homotopy preserves its underlying bar map. -/
@[simp]
theorem barHomotopy_copy {f g f' g' : AInfinityHom AA BB} (h : Homotopy f g)
    (hf : f = f') (hg : g = g') : (h.copy hf hg).barHomotopy = h.barHomotopy := (rfl)

/-- Transporting a homotopy preserves its suspended Taylor components. -/
@[simp]
theorem taylor_copy {f g f' g' : AInfinityHom AA BB} (h : Homotopy f g)
    (hf : f = f') (hg : g = g') : (h.copy hf hg).taylor = h.taylor := by
  rw [taylor_def, taylor_def, barHomotopy_copy]

/-- Transporting a homotopy preserves its arity-one chain homotopy. -/
@[simp]
theorem linearHomotopy_copy {f g f' g' : AInfinityHom AA BB} (h : Homotopy f g)
    (hf : f = f') (hg : g = g') : (h.copy hf hg).linearHomotopy = h.linearHomotopy :=
  LinearMap.ext fun a ↦ by rw [linearHomotopy_apply, linearHomotopy_apply, taylor_copy]

/-- The arity-one chain homotopy of `refl f` is zero. -/
@[simp]
theorem linearHomotopy_refl (f : AInfinityHom AA BB) : (refl f).linearHomotopy = 0 :=
  LinearMap.ext fun a ↦ by
    rw [linearHomotopy_apply, taylor_refl, LinearMap.zero_apply, LinearMap.zero_apply]

/-- The bar map of a homotopy is the `(f.barMap, g.barMap)`-coderivation Taylor expansion of its
suspended Taylor components. -/
theorem barHomotopy_eq_gradedCoderivAlong {f g : AInfinityHom AA BB} (h : Homotopy f g) :
    h.barHomotopy =
      gradedCoderivAlong (AA.grading.shift 1) 1 f.barMap g.barMap h.taylor := by
  rw [taylor_def]
  exact h.isGradedCoderivationAlong_barHomotopy.eq_gradedCoderivAlong f.isCoalgHom_barMap
    g.isCoalgHom_barMap

/-- The homotopy from `f` to `g` with prescribed suspended Taylor components `φ` of degree `-1`
satisfying the component equation. -/
noncomputable def ofTaylor {f g : AInfinityHom AA BB} (φ : ReducedTensorWords R A →ₗ[R] B)
    (hφ : LinearMap.IsHomogeneous φ (gradedPiece (AA.grading.shift 1))
      (BB.grading.shift 1).piece (-1))
    (e : f.taylor - g.taylor = BB.taylor ∘ₗ
      gradedCoderivAlong (AA.grading.shift 1) 1 f.barMap g.barMap φ +
      φ ∘ₗ AA.barDifferential) :
    Homotopy f g :=
  ofCoderivation (gradedCoderivAlong (AA.grading.shift 1) 1 f.barMap g.barMap φ)
    (isGradedCoderivationAlong_gradedCoderivAlong f.isCoalgHom_barMap g.isCoalgHom_barMap φ)
    (isHomogeneous_gradedCoderivAlong f.isHomogeneous_barMap g.isHomogeneous_barMap hφ)
    (by rwa [letter_comp_gradedCoderivAlong])

/-- The bar map of `Homotopy.ofTaylor` is `gradedCoderivAlong`. -/
@[simp]
theorem barHomotopy_ofTaylor {f g : AInfinityHom AA BB} (φ : ReducedTensorWords R A →ₗ[R] B)
    (hφ e) : (ofTaylor (f := f) (g := g) φ hφ e).barHomotopy =
      gradedCoderivAlong (AA.grading.shift 1) 1 f.barMap g.barMap φ := by
  rw [ofTaylor, barHomotopy_ofCoderivation]

/-- The Taylor map of `Homotopy.ofTaylor` recovers `φ`. -/
@[simp]
theorem taylor_ofTaylor {f g : AInfinityHom AA BB} (φ : ReducedTensorWords R A →ₗ[R] B)
    (hφ e) : (ofTaylor (f := f) (g := g) φ hφ e).taylor = φ := by
  rw [taylor_def, barHomotopy_ofTaylor, letter_comp_gradedCoderivAlong]

/-- Reconstructing a homotopy from its own Taylor map recovers the homotopy. -/
@[simp]
theorem ofTaylor_taylor {f g : AInfinityHom AA BB} (h : Homotopy f g) :
    ofTaylor h.taylor h.isHomogeneous_taylor
      (by rw [← h.barHomotopy_eq_gradedCoderivAlong]; exact h.taylor_sub_taylor) = h :=
  ext (taylor_ofTaylor _ _ _)

/-! ### Transitivity -/

private theorem barDifferential_commutator_eq_zero
    (U : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) :
    BB.barDifferential ∘ₗ (BB.barDifferential ∘ₗ U - U ∘ₗ AA.barDifferential) +
      (BB.barDifferential ∘ₗ U - U ∘ₗ AA.barDifferential) ∘ₗ AA.barDifferential = 0 := by
  simp only [LinearMap.comp_sub, LinearMap.sub_comp, ← LinearMap.comp_assoc, BB.barDifferential_sq,
    LinearMap.zero_comp]
  simp only [LinearMap.comp_assoc, AA.barDifferential_sq, LinearMap.comp_zero]
  abel

private theorem isHomogeneous_barDifferential_commutator
    {U : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B}
    (hU : LinearMap.IsHomogeneous U (gradedPiece (AA.grading.shift 1))
      (gradedPiece (BB.grading.shift 1)) (-2)) :
    LinearMap.IsHomogeneous (BB.barDifferential ∘ₗ U - U ∘ₗ AA.barDifferential)
      (gradedPiece (AA.grading.shift 1)) (gradedPiece (BB.grading.shift 1)) (-1) := by
  have h₁ : LinearMap.IsHomogeneous (BB.barDifferential ∘ₗ U)
      (gradedPiece (AA.grading.shift 1)) (gradedPiece (BB.grading.shift 1)) (-1) := by
    simpa only [show (-2 : ℤ) + 1 = -1 by decide] using BB.isHomogeneous_barDifferential.comp hU
  have h₂ : LinearMap.IsHomogeneous (U ∘ₗ AA.barDifferential)
      (gradedPiece (AA.grading.shift 1)) (gradedPiece (BB.grading.shift 1)) (-1) := by
    simpa only [show (1 : ℤ) + -2 = -1 by decide] using hU.comp AA.isHomogeneous_barDifferential
  exact h₁.sub h₂

private theorem isGradedCoderivationAlong_trans {f g k : AInfinityHom AA BB}
    (h₁ : Homotopy f g) (h₂ : Homotopy g k) :
    IsGradedCoderivationAlong (AA.grading.shift 1) 1 f.barMap k.barMap
      (h₁.barHomotopy + h₂.barHomotopy +
        (BB.barDifferential ∘ₗ
            gradedCoderivCup (AA.grading.shift 1) 1 f.barMap h₁.barHomotopy h₂.barHomotopy -
          gradedCoderivCup (AA.grading.shift 1) 1 f.barMap h₁.barHomotopy h₂.barHomotopy ∘ₗ
            AA.barDifferential)) := by
  set U := gradedCoderivCup (AA.grading.shift 1) 1 f.barMap h₁.barHomotopy h₂.barHomotopy
  have hU_hom : LinearMap.IsHomogeneous U (gradedPiece (AA.grading.shift 1))
      (gradedPiece (BB.grading.shift 1)) (-2) :=
    isHomogeneous_gradedCoderivCup f.isHomogeneous_barMap h₁.isHomogeneous_barHomotopy
      h₂.isHomogeneous_barHomotopy
  have hU_dec := fun w ↦ LinearMap.congr_fun (deconcatenation_comp_gradedCoderivCup
    f.isCoalgHom_barMap g.isCoalgHom_barMap h₁.isGradedCoderivationAlong_barHomotopy
    h₂.isGradedCoderivationAlong_barHomotopy) w
  simp only [LinearMap.comp_apply, LinearMap.add_apply] at hU_dec
  have hU_dec' : ∀ w, deconcatenation R B (U w) =
      TensorProduct.map U k.barMap (deconcatenation R A w) +
        TensorProduct.map h₁.barHomotopy h₂.barHomotopy
          (LinearMap.rTensor _ (map R ((AA.grading.shift 1).koszulTwist 1))
            (deconcatenation R A w)) +
        TensorProduct.map f.barMap U (deconcatenation R A w) := fun w ↦ by
    rw [hU_dec w, ← LinearMap.comp_apply (TensorProduct.map h₁.barHomotopy h₂.barHomotopy),
      LinearMap.rTensor_def, ← TensorProduct.map_comp, LinearMap.comp_id]
  rw [isGradedCoderivationAlong_iff]
  refine LinearMap.ext fun z ↦ ?_
  have hW := deconcatenation_comp_sub_comp_of_cup hU_hom (by decide) h₁.isHomogeneous_barHomotopy
    (by decide) AA.isGradedCoderivation_barDifferential AA.isHomogeneous_barDifferential (by decide)
    BB.isGradedCoderivation_barDifferential f.isHomogeneous_barMap f.barDifferential_comp_barMap
    k.barDifferential_comp_barMap (hU_dec' z) (hU_dec' (AA.barDifferential z))
  rw [← h₁.barMap_sub_barMap, ← h₂.barMap_sub_barMap] at hW
  simp only [LinearMap.comp_apply, LinearMap.add_apply]
  rw [map_add, map_add, h₁.isGradedCoderivationAlong_barHomotopy.deconcatenation_apply,
    h₂.isGradedCoderivationAlong_barHomotopy.deconcatenation_apply, hW]
  induction deconcatenation R A z using TensorProduct.inductionOn with
  | tmul u v =>
      simp only [TensorProduct.map_tmul, LinearMap.rTensor_tmul, LinearMap.add_apply,
        LinearMap.sub_apply, TensorProduct.add_tmul, TensorProduct.tmul_add,
        TensorProduct.sub_tmul, TensorProduct.tmul_sub]
      abel
  | add u v hu hv =>
      simp only [map_add] at hu hv ⊢
      convert congrArg₂ (· + ·) hu hv using 1 <;> abel

/-- **Vertical composition of `A∞` homotopies.**  Given homotopies from `f` to `g` and from `g` to
`k`, adding the bar commutator of their cup operator corrects `H₁ + H₂` to a homotopy from `f` to
`k`. -/
noncomputable def trans {f g k : AInfinityHom AA BB} (h₁ : Homotopy f g) (h₂ : Homotopy g k) :
    Homotopy f k where
  barHomotopy := h₁.barHomotopy + h₂.barHomotopy +
    (BB.barDifferential ∘ₗ
        gradedCoderivCup (AA.grading.shift 1) 1 f.barMap h₁.barHomotopy h₂.barHomotopy -
      gradedCoderivCup (AA.grading.shift 1) 1 f.barMap h₁.barHomotopy h₂.barHomotopy ∘ₗ
        AA.barDifferential)
  isGradedCoderivationAlong_barHomotopy := isGradedCoderivationAlong_trans h₁ h₂
  isHomogeneous_barHomotopy :=
    (h₁.isHomogeneous_barHomotopy.add h₂.isHomogeneous_barHomotopy).add
      (isHomogeneous_barDifferential_commutator
        (isHomogeneous_gradedCoderivCup f.isHomogeneous_barMap h₁.isHomogeneous_barHomotopy
          h₂.isHomogeneous_barHomotopy))
  barMap_sub_barMap := by
    rw [LinearMap.comp_add, LinearMap.comp_add, LinearMap.add_comp, LinearMap.add_comp]
    have h0 := barDifferential_commutator_eq_zero (AA := AA) (BB := BB)
      (gradedCoderivCup (AA.grading.shift 1) 1 f.barMap h₁.barHomotopy h₂.barHomotopy)
    calc
      f.barMap - k.barMap = (f.barMap - g.barMap) + (g.barMap - k.barMap) + 0 := by abel
      _ = _ := by
        rw [h₁.barMap_sub_barMap, h₂.barMap_sub_barMap, ← h0]
        abel

/-- The bar map of a vertical composite homotopy `h₁.trans h₂`. -/
@[simp]
theorem barHomotopy_trans {f g k : AInfinityHom AA BB} (h₁ : Homotopy f g) (h₂ : Homotopy g k) :
    (h₁.trans h₂).barHomotopy =
      h₁.barHomotopy + h₂.barHomotopy +
        (BB.barDifferential ∘ₗ
            gradedCoderivCup (AA.grading.shift 1) 1 f.barMap h₁.barHomotopy h₂.barHomotopy -
           gradedCoderivCup (AA.grading.shift 1) 1 f.barMap h₁.barHomotopy h₂.barHomotopy ∘ₗ
             AA.barDifferential) := (rfl)

/-- On arity one, vertical composition of `A∞` homotopies adds their linear chain homotopies. -/
@[simp]
theorem linearHomotopy_trans {f g k : AInfinityHom AA BB} (h₁ : Homotopy f g) (h₂ : Homotopy g k) :
    (h₁.trans h₂).linearHomotopy = h₁.linearHomotopy + h₂.linearHomotopy := by
  refine LinearMap.ext fun a ↦ ?_
  simp only [linearHomotopy_apply, taylor_def, barHomotopy_trans, LinearMap.comp_apply,
    LinearMap.add_apply, LinearMap.sub_apply, AInfinityAlgebra.barDifferential_ofLetter,
    gradedCoderivCup_ofLetter, map_zero, sub_zero, add_zero, map_add]

/-! ### Symmetry -/

private noncomputable def symmSeq {f g : AInfinityHom AA BB} (h : Homotopy f g) :
    ℕ → ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B
  | 0 => -h.barHomotopy
  | n + 1 =>
    -h.barHomotopy -
      (BB.barDifferential ∘ₗ
          gradedCoderivCup (AA.grading.shift 1) 1 f.barMap h.barHomotopy (symmSeq h n) -
        gradedCoderivCup (AA.grading.shift 1) 1 f.barMap h.barHomotopy (symmSeq h n) ∘ₗ
          AA.barDifferential)

private theorem isHomogeneous_symmSeq {f g : AInfinityHom AA BB} (h : Homotopy f g) (n : ℕ) :
    LinearMap.IsHomogeneous (symmSeq h n) (gradedPiece (AA.grading.shift 1))
      (gradedPiece (BB.grading.shift 1)) (-1) := by
  induction n with
  | zero => exact h.isHomogeneous_barHomotopy.neg
  | succ n ih =>
      exact h.isHomogeneous_barHomotopy.neg.sub
        (isHomogeneous_barDifferential_commutator
          (isHomogeneous_gradedCoderivCup f.isHomogeneous_barMap h.isHomogeneous_barHomotopy ih))

private theorem symmSeq_succ {f g : AInfinityHom AA BB} (h : Homotopy f g) (n : ℕ) :
    symmSeq h (n + 1) =
      -h.barHomotopy -
        (BB.barDifferential ∘ₗ
            gradedCoderivCup (AA.grading.shift 1) 1 f.barMap h.barHomotopy (symmSeq h n) -
          gradedCoderivCup (AA.grading.shift 1) 1 f.barMap h.barHomotopy (symmSeq h n) ∘ₗ
            AA.barDifferential) := (rfl)

private theorem symmSeq_succ_apply_of_mem_filtration {f g : AInfinityHom AA BB} (h : Homotopy f g) :
    ∀ n, ∀ z ∈ filtration R A n, symmSeq h (n + 1) z = symmSeq h n z := by
  intro n
  induction n with
  | zero =>
      intro z hz
      rw [filtration_zero, Submodule.mem_bot] at hz
      rw [hz, map_zero, map_zero]
  | succ n ih =>
      intro z hz
      conv_lhs => rw [symmSeq_succ]
      conv_rhs => rw [symmSeq_succ]
      simp only [LinearMap.sub_apply, LinearMap.comp_apply]
      rw [gradedCoderivCup_apply_eq_of_mem_filtration _ _ _ _ (ih ·) hz,
        gradedCoderivCup_apply_eq_of_mem_filtration _ _ _ _ (ih ·)
          (AA.barDifferential_mem_filtration hz)]

private theorem symmSeq_apply_eq_of_le {f g : AInfinityHom AA BB} (h : Homotopy f g)
    {k n : ℕ} (hkn : k ≤ n) {z : ReducedTensorWords R A} (hz : z ∈ filtration R A k) :
    symmSeq h n z = symmSeq h k z := by
  induction n, hkn using Nat.le_induction with
  | base => rfl
  | succ n hkn ih =>
      rw [symmSeq_succ_apply_of_mem_filtration h n z (filtration_monotone R A hkn hz), ih]

private noncomputable def symmBarHomotopy {f g : AInfinityHom AA BB} (h : Homotopy f g) :
    ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B :=
  DirectSum.toModule R {k : ℕ // 0 < k} _ fun k ↦ symmSeq h k.1 ∘ₗ of R A k

private theorem symmBarHomotopy_apply_of_mem_filtration {f g : AInfinityHom AA BB}
    (h : Homotopy f g) {n : ℕ} {z : ReducedTensorWords R A} (hz : z ∈ filtration R A n) :
    symmBarHomotopy h z = symmSeq h n z := by
  suffices hle : filtration R A n ≤ LinearMap.eqLocus (symmBarHomotopy h) (symmSeq h n) from hle hz
  rw [filtration_le_iff]
  rintro k hk _ ⟨x, rfl⟩
  rw [LinearMap.mem_eqLocus, symmBarHomotopy, toModule_of, LinearMap.comp_apply,
    symmSeq_apply_eq_of_le h hk (of_mem_filtration R A le_rfl x)]

private theorem symmBarHomotopy_eq {f g : AInfinityHom AA BB} (h : Homotopy f g) :
    symmBarHomotopy h =
      -h.barHomotopy -
        (BB.barDifferential ∘ₗ
            gradedCoderivCup (AA.grading.shift 1) 1 f.barMap h.barHomotopy (symmBarHomotopy h) -
          gradedCoderivCup (AA.grading.shift 1) 1 f.barMap h.barHomotopy (symmBarHomotopy h) ∘ₗ
            AA.barDifferential) := by
  refine LinearMap.ext fun z ↦ ?_
  obtain ⟨n, hn⟩ := exists_mem_filtration R A z
  have hz : z ∈ filtration R A (n + 1) := filtration_monotone R A n.le_succ hn
  rw [symmBarHomotopy_apply_of_mem_filtration h hz, symmSeq_succ]
  simp only [LinearMap.sub_apply, LinearMap.comp_apply]
  rw [gradedCoderivCup_apply_eq_of_mem_filtration _ _ _ _
      (fun w hw ↦ (symmBarHomotopy_apply_of_mem_filtration h hw).symm) hz,
    gradedCoderivCup_apply_eq_of_mem_filtration _ _ _ _
      (fun w hw ↦ (symmBarHomotopy_apply_of_mem_filtration h hw).symm)
      (AA.barDifferential_mem_filtration hz)]

private theorem isHomogeneous_symmBarHomotopy {f g : AInfinityHom AA BB} (h : Homotopy f g) :
    LinearMap.IsHomogeneous (symmBarHomotopy h) (gradedPiece (AA.grading.shift 1))
      (gradedPiece (BB.grading.shift 1)) (-1) := by
  rw [LinearMap.isHomogeneous_def]
  intro p z hz
  obtain ⟨n, hn⟩ := exists_mem_filtration R A z
  rw [symmBarHomotopy_apply_of_mem_filtration h hn]
  exact (isHomogeneous_symmSeq h n).map_mem hz

private theorem barMap_sub_barMap_symmBarHomotopy {f g : AInfinityHom AA BB} (h : Homotopy f g) :
    g.barMap - f.barMap =
      BB.barDifferential ∘ₗ symmBarHomotopy h + symmBarHomotopy h ∘ₗ AA.barDifferential := by
  set W := BB.barDifferential ∘ₗ
      gradedCoderivCup (AA.grading.shift 1) 1 f.barMap h.barHomotopy (symmBarHomotopy h) -
    gradedCoderivCup (AA.grading.shift 1) 1 f.barMap h.barHomotopy (symmBarHomotopy h) ∘ₗ
      AA.barDifferential
  have heq : symmBarHomotopy h = -h.barHomotopy - W := symmBarHomotopy_eq h
  have h0 : BB.barDifferential ∘ₗ W + W ∘ₗ AA.barDifferential = 0 :=
    barDifferential_commutator_eq_zero _
  calc
    g.barMap - f.barMap = -(f.barMap - g.barMap) - 0 := by abel
    _ = -(BB.barDifferential ∘ₗ h.barHomotopy + h.barHomotopy ∘ₗ AA.barDifferential) -
          (BB.barDifferential ∘ₗ W + W ∘ₗ AA.barDifferential) := by
      rw [h.barMap_sub_barMap, h0]
    _ = BB.barDifferential ∘ₗ symmBarHomotopy h + symmBarHomotopy h ∘ₗ AA.barDifferential := by
      conv_rhs =>
        rw [heq, LinearMap.comp_sub, LinearMap.comp_neg, LinearMap.sub_comp, LinearMap.neg_comp]
      abel

private theorem deconcatenation_symmBarHomotopy_succ {f g : AInfinityHom AA BB}
    (h : Homotopy f g) {n : ℕ}
    (ih : ∀ z ∈ filtration R A n,
      deconcatenation R B (symmBarHomotopy h z) =
        TensorProduct.map (symmBarHomotopy h) f.barMap (deconcatenation R A z) +
          TensorProduct.map g.barMap (symmBarHomotopy h)
            (LinearMap.rTensor _ (map R ((AA.grading.shift 1).koszulTwist 1))
              (deconcatenation R A z)))
    {z : ReducedTensorWords R A} (hz : z ∈ filtration R A (n + 1)) :
    deconcatenation R B (symmBarHomotopy h z) =
      TensorProduct.map (symmBarHomotopy h) f.barMap (deconcatenation R A z) +
        TensorProduct.map g.barMap (symmBarHomotopy h)
          (LinearMap.rTensor _ (map R ((AA.grading.shift 1).koszulTwist 1))
            (deconcatenation R A z)) := by
  set H' := symmBarHomotopy h
  set V := gradedCoderivCup (AA.grading.shift 1) 1 f.barMap h.barHomotopy H'
  have hV_hom : LinearMap.IsHomogeneous V (gradedPiece (AA.grading.shift 1))
      (gradedPiece (BB.grading.shift 1)) (-2) :=
    isHomogeneous_gradedCoderivCup f.isHomogeneous_barMap h.isHomogeneous_barHomotopy
      (isHomogeneous_symmBarHomotopy h)
  have hV_dec : ∀ w ∈ filtration R A (n + 1), deconcatenation R B (V w) =
      TensorProduct.map V f.barMap (deconcatenation R A w) +
        TensorProduct.map h.barHomotopy H'
          (LinearMap.rTensor _ (map R ((AA.grading.shift 1).koszulTwist 1))
            (deconcatenation R A w)) +
        TensorProduct.map f.barMap V (deconcatenation R A w) := fun w hw ↦ by
    rw [deconcatenation_gradedCoderivCup_of_mem_filtration f.isCoalgHom_barMap
        g.isCoalgHom_barMap h.isGradedCoderivationAlong_barHomotopy ih hw,
      ← LinearMap.comp_apply (TensorProduct.map h.barHomotopy H'),
      LinearMap.rTensor_def, ← TensorProduct.map_comp, LinearMap.comp_id]
  have hW := deconcatenation_comp_sub_comp_of_cup hV_hom (by decide)
    h.isHomogeneous_barHomotopy (by decide) AA.isGradedCoderivation_barDifferential
    AA.isHomogeneous_barDifferential (by decide) BB.isGradedCoderivation_barDifferential
    f.isHomogeneous_barMap f.barDifferential_comp_barMap f.barDifferential_comp_barMap
    (hV_dec z hz) (hV_dec _ (AA.barDifferential_mem_filtration hz))
  rw [← h.barMap_sub_barMap, ← barMap_sub_barMap_symmBarHomotopy h] at hW
  have hH'_eq : ∀ w, H' w = -h.barHomotopy w -
      (BB.barDifferential ∘ₗ V - V ∘ₗ AA.barDifferential) w :=
    LinearMap.congr_fun (symmBarHomotopy_eq h)
  rw [hH'_eq z, map_sub, map_neg, h.isGradedCoderivationAlong_barHomotopy.deconcatenation_apply, hW]
  induction deconcatenation R A z using TensorProduct.inductionOn with
  | tmul u v =>
      simp only [TensorProduct.map_tmul, LinearMap.rTensor_tmul, LinearMap.sub_apply,
        hH'_eq, TensorProduct.neg_tmul, TensorProduct.tmul_neg, TensorProduct.sub_tmul,
        TensorProduct.tmul_sub]
      abel
  | add u v hu hv =>
      simp only [map_add] at hu hv ⊢
      convert congrArg₂ (· + ·) hu hv using 1 <;> abel

private theorem isGradedCoderivationAlong_symmBarHomotopy {f g : AInfinityHom AA BB}
    (h : Homotopy f g) :
    IsGradedCoderivationAlong (AA.grading.shift 1) 1 g.barMap f.barMap (symmBarHomotopy h) := by
  have key : ∀ n, ∀ z ∈ filtration R A n,
      deconcatenation R B (symmBarHomotopy h z) =
        TensorProduct.map (symmBarHomotopy h) f.barMap (deconcatenation R A z) +
          TensorProduct.map g.barMap (symmBarHomotopy h)
            (LinearMap.rTensor _ (map R ((AA.grading.shift 1).koszulTwist 1))
              (deconcatenation R A z)) := by
    intro n
    induction n with
    | zero =>
        intro z hz
        rw [filtration_zero, Submodule.mem_bot] at hz
        rw [hz]; simp only [map_zero, add_zero]
    | succ n ih => exact fun _ hz ↦ deconcatenation_symmBarHomotopy_succ h ih hz
  rw [isGradedCoderivationAlong_iff]
  refine LinearMap.ext fun z ↦ ?_
  obtain ⟨n, hn⟩ := exists_mem_filtration R A z
  exact key n z hn

/-- **Reversal of an `A∞` homotopy.**  Solving `h.trans h' = refl f` recursively by word length
yields a homotopy from `g` back to `f`. -/
noncomputable def symm {f g : AInfinityHom AA BB} (h : Homotopy f g) : Homotopy g f where
  barHomotopy := symmBarHomotopy h
  isGradedCoderivationAlong_barHomotopy := isGradedCoderivationAlong_symmBarHomotopy h
  isHomogeneous_barHomotopy := isHomogeneous_symmBarHomotopy h
  barMap_sub_barMap := barMap_sub_barMap_symmBarHomotopy h

private theorem barHomotopy_symm {f g : AInfinityHom AA BB} (h : Homotopy f g) :
    h.symm.barHomotopy = symmBarHomotopy h := (rfl)

/-- Composing a homotopy with its reversal produces the zero homotopy `refl f`. -/
@[simp]
theorem trans_symm {f g : AInfinityHom AA BB} (h : Homotopy f g) : h.trans h.symm = refl f := by
  apply barHomotopy_injective
  rw [barHomotopy_trans, barHomotopy_refl, barHomotopy_symm]
  conv_lhs => enter [1, 2]; rw [symmBarHomotopy_eq h]
  abel

/-- On arity one, reversing an `A∞` homotopy negates its linear chain homotopy. -/
@[simp]
theorem linearHomotopy_symm {f g : AInfinityHom AA BB} (h : Homotopy f g) :
    h.symm.linearHomotopy = -h.linearHomotopy := by
  have e := congrArg linearHomotopy (trans_symm h)
  rw [linearHomotopy_trans, linearHomotopy_refl] at e
  exact eq_neg_of_add_eq_zero_right e

end Homotopy

/-! ### The homotopy equivalence relation on morphisms -/

/-- Two `A∞` morphisms `f` and `g` are **homotopic** when there exists a homotopy between them. -/
def Homotopic (f g : AInfinityHom AA BB) : Prop :=
  Nonempty (Homotopy f g)

/-- Unfolding lemma for `Homotopic`. -/
theorem homotopic_def (f g : AInfinityHom AA BB) :
    f.Homotopic g ↔ Nonempty (Homotopy f g) :=
  Iff.rfl

/-- Any explicit homotopy witnesses that its endpoints are homotopic. -/
theorem Homotopy.homotopic {f g : AInfinityHom AA BB} (h : Homotopy f g) : f.Homotopic g :=
  ⟨h⟩

/-- Homotopy of `A∞` morphisms is reflexive. -/
@[refl]
theorem Homotopic.refl (f : AInfinityHom AA BB) : f.Homotopic f :=
  ⟨Homotopy.refl f⟩

/-- Homotopy of `A∞` morphisms is symmetric. -/
@[symm]
theorem Homotopic.symm {f g : AInfinityHom AA BB} (h : f.Homotopic g) : g.Homotopic f :=
  let ⟨H⟩ := h
  ⟨H.symm⟩

/-- Homotopy of `A∞` morphisms is transitive. -/
theorem Homotopic.trans {f g k : AInfinityHom AA BB} (h₁ : f.Homotopic g) (h₂ : g.Homotopic k) :
    f.Homotopic k :=
  let ⟨H₁⟩ := h₁
  let ⟨H₂⟩ := h₂
  ⟨H₁.trans H₂⟩

/-- `Homotopic` is an equivalence relation on `AInfinityHom AA BB`. -/
theorem equivalence_homotopic : Equivalence (Homotopic (AA := AA) (BB := BB)) :=
  ⟨Homotopic.refl, Homotopic.symm, Homotopic.trans⟩

/-- Postcomposing homotopic `A∞` morphisms with a morphism preserves homotopy. -/
theorem Homotopic.compRight {f g : AInfinityHom AA BB} (h : f.Homotopic g)
    (k : AInfinityHom BB CC) : (k.comp f).Homotopic (k.comp g) :=
  let ⟨H⟩ := h
  ⟨H.compRight k⟩

/-- Precomposing homotopic `A∞` morphisms with a morphism preserves homotopy. -/
theorem Homotopic.compLeft {f g : AInfinityHom AA BB} (h : f.Homotopic g)
    (k : AInfinityHom CC AA) : (f.comp k).Homotopic (g.comp k) :=
  let ⟨H⟩ := h
  ⟨H.compLeft k⟩

/-- Horizontal composition of `A∞` morphisms respects homotopy in both arguments. -/
theorem Homotopic.comp {f₁ f₂ : AInfinityHom BB CC} {g₁ g₂ : AInfinityHom AA BB}
    (hf : f₁.Homotopic f₂) (hg : g₁.Homotopic g₂) :
    (f₁.comp g₁).Homotopic (f₂.comp g₂) :=
  (hf.compLeft g₁).trans (hg.compRight f₂)

/-- Homotopic `A∞` morphisms induce the same map on cohomology. -/
theorem Homotopic.cohomologyMap_eq {f g : AInfinityHom AA BB} (h : f.Homotopic g) :
    f.cohomologyMap = g.cohomologyMap :=
  let ⟨H⟩ := h
  H.cohomologyMap_eq

/-- Homotopic `A∞` morphisms are quasi-isomorphisms together. -/
theorem Homotopic.isQuasiIso_iff {f g : AInfinityHom AA BB} (h : f.Homotopic g) :
    f.IsQuasiIso ↔ g.IsQuasiIso :=
  let ⟨H⟩ := h
  H.isQuasiIso_iff

end AInfinityHom

end TauCeti
