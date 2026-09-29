/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Linear
public import TauCeti.Algebra.Homology.LinearYoneda
public import TauCeti.Algebra.Homology.Monoidal.Summand
public import TauCeti.Algebra.Homology.Monoidal.TensorDifferential
public import TauCeti.CategoryTheory.Monoidal.Preadditive

/-!
# Cup products of cochains along a diagonal

Let `C` be a `k`-linear abelian monoidal category, let `A`, `B` and `E` be chain complexes in `C`
indexed by `ℕ`, and let `D : E ⟶ A ⊗ B` be a chain map, a *diagonal*.  Given a pairing
`μ : M ⊗ N ⟶ P` of coefficient objects, a cochain `φ : A_p ⟶ M` and a cochain `ψ : B_q ⟶ N`
have the cup product `φ ⌣ ψ : E_n ⟶ P`, for `p + q = n`: the degree-`n` component of `D`, followed
by the projection of `(A ⊗ B)_n` onto its summand `A_p ⊗ B_q`, by `φ ⊗ ψ` and by `μ`.  Since `D`
is a chain map and the tensor product carries the Koszul signs, it satisfies the Leibniz rule
`(φ ⌣ ψ) ∘ d = (φ ∘ d) ⌣ ψ + (-1)^p φ ⌣ (ψ ∘ d)`.  Hence a cocycle cupped with a cocycle is a
cocycle, a coboundary cupped with a cocycle (in either order) is a coboundary, and the cup
product descends to a `k`-bilinear map `Hᵖ(Hom(A, M)) × H^q(Hom(B, N)) ⟶ Hⁿ(Hom(E, P))` on the
cohomology of the complexes `ChainComplex.linearYonedaObj`.  It is natural along maps of
diagonals.

The singular cup product is the case where `D` is the Alexander–Whitney map precomposed with the
diagonal of a space; there `φ ⌣ ψ` evaluates a singular simplex on its front `p`-face and its back
`q`-face.

## Main definitions and results

* `TauCeti.ChainComplex.tensorCochain`: the morphism `(A ⊗ B)_n ⟶ P` given on the summand
  `A_p ⊗ B_q` by `φ ⊗ ψ` and `μ`, with its Leibniz rule
  `TauCeti.ChainComplex.d_comp_tensorCochain`.
* `TauCeti.ChainComplex.cupCochain`: the cup product of cochains.
* `TauCeti.ChainComplex.d_comp_cupCochain`: the Leibniz rule.
* `TauCeti.ChainComplex.cupCochain_naturality`: naturality along a map of diagonals.
* `TauCeti.ChainComplex.cup`: the cup product on cohomology, with
  `TauCeti.ChainComplex.cup_homologyπ` computing it on classes of cocycles and
  `TauCeti.ChainComplex.cup_naturality` its naturality.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.2, Lemma 3.6.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex

namespace TauCeti.ChainComplex

variable {C : Type*} [Category* C] [Abelian C]

section Extend

variable {A : ChainComplex C ℕ} {M : C}

/-- A morphism `A_p ⟶ M` as a family of morphisms `A_i ⟶ M` in all degrees, zero away from `p`. -/
private def extendCochain {p : ℕ} (φ : A.X p ⟶ M) (i : ℕ) : A.X i ⟶ M :=
  if h : i = p then (A.XIsoOfEq h).hom ≫ φ else 0

private lemma extendCochain_self {p : ℕ} (φ : A.X p ⟶ M) : extendCochain φ p = φ := by
  simp [extendCochain]

private lemma extendCochain_of_ne {p i : ℕ} (φ : A.X p ⟶ M) (h : i ≠ p) :
    extendCochain φ i = 0 :=
  dite_eq_right h

/-- Extending `φ ∘ d` by zero is precomposing the extension of `φ` with the differential. -/
private lemma extendCochain_d_comp {p : ℕ} (φ : A.X p ⟶ M) (i : ℕ) :
    extendCochain (A.d (p + 1) p ≫ φ) (i + 1) = A.d (i + 1) i ≫ extendCochain φ i := by
  by_cases h : i = p
  · subst h
    simp [extendCochain_self]
  · rw [extendCochain_of_ne _ (by omega), extendCochain_of_ne _ h, comp_zero]

private lemma extendCochain_d_comp_zero {p : ℕ} (φ : A.X p ⟶ M) :
    extendCochain (A.d (p + 1) p ≫ φ) 0 = 0 :=
  extendCochain_of_ne _ (by omega)

/-- The sign `(-1)^i` on the extension of a cochain of degree `p` is `(-1)^p`. -/
private lemma zsmul_extendCochain {p : ℕ} (φ : A.X p ⟶ M) (i : ℕ) :
    ((-1 : ℤ) ^ i) • extendCochain φ i = ((-1 : ℤ) ^ p) • extendCochain φ i := by
  by_cases h : i = p
  · rw [h]
  · simp [extendCochain_of_ne _ h]

private lemma extendCochain_add {p : ℕ} (φ φ' : A.X p ⟶ M) (i : ℕ) :
    extendCochain (φ + φ') i = extendCochain φ i + extendCochain φ' i := by
  by_cases h : i = p
  · subst h
    simp [extendCochain_self]
  · simp [extendCochain_of_ne _ h]

private lemma extendCochain_smul {k : Type*} [Ring k] [Linear k C] {p : ℕ} (r : k)
    (φ : A.X p ⟶ M) (i : ℕ) :
    extendCochain (r • φ) i = r • extendCochain φ i := by
  by_cases h : i = p
  · subst h
    simp [extendCochain_self]
  · simp [extendCochain_of_ne _ h]

private lemma extendCochain_comp {A' : ChainComplex C ℕ} (g : A' ⟶ A) {p : ℕ} (φ : A.X p ⟶ M)
    (i : ℕ) : extendCochain (g.f p ≫ φ) i = g.f i ≫ extendCochain φ i := by
  by_cases h : i = p
  · subst h
    simp [extendCochain_self]
  · simp [extendCochain_of_ne _ h]

end Extend

variable [MonoidalCategory C] [MonoidalPreadditive C] {A B E : ChainComplex C ℕ} {M N P : C}

section Tensor

variable (μ : M ⊗ N ⟶ P)

/-- **The tensor product of cochains**: for cochains `φ : A_p ⟶ M` and `ψ : B_q ⟶ N`, the morphism
`(A ⊗ B)_n ⟶ P` which on the summand `A_p ⊗ B_q` is `φ ⊗ ψ` followed by the pairing `μ`
(`TauCeti.ChainComplex.ιTensorObj_tensorCochain`) and vanishes on every other summand
(`TauCeti.ChainComplex.ιTensorObj_tensorCochain_of_ne`). -/
def tensorCochain {p q : ℕ} (φ : A.X p ⟶ M) (ψ : B.X q ⟶ N) (n : ℕ) : (A ⊗ B).X n ⟶ P :=
  mapBifunctorDesc fun i j _ ↦ (extendCochain φ i ⊗ₘ extendCochain ψ j) ≫ μ

@[reassoc]
private lemma ιTensorObj_tensorCochain_extend {p q : ℕ} (φ : A.X p ⟶ M) (ψ : B.X q ⟶ N)
    (i j n : ℕ) (h : i + j = n) :
    ιTensorObj A B i j n h ≫ tensorCochain μ φ ψ n =
      (extendCochain φ i ⊗ₘ extendCochain ψ j) ≫ μ :=
  ι_mapBifunctorDesc _ _ _ _

/-- The tensor product of cochains `φ : A_p ⟶ M` and `ψ : B_q ⟶ N` is `φ ⊗ ψ` followed by `μ` on
the summand `A_p ⊗ B_q`. -/
@[reassoc (attr := simp)]
lemma ιTensorObj_tensorCochain {p q : ℕ} (φ : A.X p ⟶ M) (ψ : B.X q ⟶ N) (n : ℕ)
    (h : p + q = n) :
    ιTensorObj A B p q n h ≫ tensorCochain μ φ ψ n = (φ ⊗ₘ ψ) ≫ μ := by
  rw [ιTensorObj_tensorCochain_extend, extendCochain_self, extendCochain_self]

/-- The tensor product of cochains `φ : A_p ⟶ M` and `ψ : B_q ⟶ N` vanishes on the summands
`A_i ⊗ B_j` with `i ≠ p`. -/
@[reassoc]
lemma ιTensorObj_tensorCochain_of_ne {p q : ℕ} (φ : A.X p ⟶ M) (ψ : B.X q ⟶ N) {i j n : ℕ}
    (h : i + j = n) (hi : i ≠ p) :
    ιTensorObj A B i j n h ≫ tensorCochain μ φ ψ n = 0 := by
  rw [ιTensorObj_tensorCochain_extend, extendCochain_of_ne _ hi, MonoidalPreadditive.zero_tensor,
    zero_comp]

/-- **The Leibniz rule for the tensor product of cochains**: precomposed with the differential of
`A ⊗ B`, the tensor product of `φ` and `ψ` is the tensor product of `φ ∘ d` and `ψ` plus `(-1)^p`
times the tensor product of `φ` and `ψ ∘ d`. -/
lemma d_comp_tensorCochain {p q : ℕ} (φ : A.X p ⟶ M) (ψ : B.X q ⟶ N) (n : ℕ) :
    (A ⊗ B).d (n + 1) n ≫ tensorCochain μ φ ψ n =
      tensorCochain μ (A.d (p + 1) p ≫ φ) ψ (n + 1) +
        ((-1 : ℤ) ^ p) • tensorCochain μ φ (B.d (q + 1) q ≫ ψ) (n + 1) := by
  refine mapBifunctor.hom_ext fun i j (h : i + j = n + 1) ↦ ?_
  -- `ιMapBifunctor` for `curriedTensor` is `ιTensorObj` by definition
  change ιTensorObj A B i j (n + 1) h ≫ _ = ιTensorObj A B i j (n + 1) h ≫ _
  have hd : (A ⊗ B).d (n + 1) n =
      mapBifunctor.D₁ A B (curriedTensor C) (ComplexShape.down ℕ) (n + 1) n +
        mapBifunctor.D₂ A B (curriedTensor C) (ComplexShape.down ℕ) (n + 1) n :=
    mapBifunctor.d_eq _ _ _ _ _ _
  rw [hd]
  obtain _ | r := i
  · obtain _ | s := j
    · omega
    obtain rfl : s = n := by omega
    simp only [Preadditive.add_comp, Preadditive.comp_add, Preadditive.comp_zsmul,
      ChainComplex.ιTensorObj_D₁_zero_assoc, ChainComplex.ιTensorObj_D₂_succ_assoc,
      Preadditive.zsmul_comp, Category.assoc, ιTensorObj_tensorCochain_extend,
      extendCochain_d_comp_zero, extendCochain_d_comp, MonoidalPreadditive.zero_tensor,
      zero_comp, zero_add, whiskerLeft_comp_tensorHom_assoc]
    rw [← Preadditive.zsmul_comp, ← Preadditive.zsmul_comp, ← zsmul_tensorHom, ← zsmul_tensorHom,
      zsmul_extendCochain]
  · obtain _ | s := j
    · obtain rfl : r = n := by omega
      simp only [Preadditive.add_comp, Preadditive.comp_add, Preadditive.comp_zsmul,
        ChainComplex.ιTensorObj_D₁_succ_assoc, ChainComplex.ιTensorObj_D₂_zero_assoc,
        ιTensorObj_tensorCochain_extend, extendCochain_d_comp_zero, extendCochain_d_comp,
        MonoidalPreadditive.tensor_zero, zero_comp, smul_zero, add_zero,
        whiskerRight_comp_tensorHom_assoc]
    · simp only [Preadditive.add_comp, Preadditive.comp_add, Preadditive.comp_zsmul,
        ChainComplex.ιTensorObj_D₁_succ_assoc, ChainComplex.ιTensorObj_D₂_succ_assoc,
        Preadditive.zsmul_comp, Category.assoc, ιTensorObj_tensorCochain_extend,
        extendCochain_d_comp, whiskerRight_comp_tensorHom_assoc, whiskerLeft_comp_tensorHom_assoc]
      rw [← Preadditive.zsmul_comp, ← Preadditive.zsmul_comp, ← zsmul_tensorHom,
        ← zsmul_tensorHom, zsmul_extendCochain]

/-- The tensor product of cochains is natural: precomposing it with the tensor product of chain
maps `f : A' ⟶ A` and `g : B' ⟶ B` is the tensor product of the precomposed cochains. -/
@[reassoc]
lemma tensorHom_f_comp_tensorCochain {A' B' : ChainComplex C ℕ} (f : A' ⟶ A) (g : B' ⟶ B)
    {p q : ℕ} (φ : A.X p ⟶ M) (ψ : B.X q ⟶ N) (n : ℕ) :
    (f ⊗ₘ g).f n ≫ tensorCochain μ φ ψ n = tensorCochain μ (f.f p ≫ φ) (g.f q ≫ ψ) n := by
  refine mapBifunctor.hom_ext fun i j (h : i + j = n) ↦ ?_
  change ιTensorObj A' B' i j n h ≫ _ = ιTensorObj A' B' i j n h ≫ _
  rw [tensorHom_eq_mapBifunctorMap, ι_tensorHom_assoc, ιTensorObj_tensorCochain_extend,
    ιTensorObj_tensorCochain_extend, extendCochain_comp, extendCochain_comp,
    tensorHom_comp_tensorHom_assoc]

variable {k : Type*} [CommRing k] [Linear k C] [MonoidalLinear k C]

private lemma tensorCochain_add_left {p q : ℕ} (φ φ' : A.X p ⟶ M) (ψ : B.X q ⟶ N) (n : ℕ) :
    tensorCochain μ (φ + φ') ψ n = tensorCochain μ φ ψ n + tensorCochain μ φ' ψ n := by
  refine mapBifunctor.hom_ext fun i j (h : i + j = n) ↦ ?_
  change ιTensorObj A B i j n h ≫ _ = ιTensorObj A B i j n h ≫ _
  simp only [Preadditive.comp_add, ιTensorObj_tensorCochain_extend, extendCochain_add,
    MonoidalPreadditive.add_tensor, Preadditive.add_comp]

private lemma tensorCochain_add_right {p q : ℕ} (φ : A.X p ⟶ M) (ψ ψ' : B.X q ⟶ N) (n : ℕ) :
    tensorCochain μ φ (ψ + ψ') n = tensorCochain μ φ ψ n + tensorCochain μ φ ψ' n := by
  refine mapBifunctor.hom_ext fun i j (h : i + j = n) ↦ ?_
  change ιTensorObj A B i j n h ≫ _ = ιTensorObj A B i j n h ≫ _
  simp only [Preadditive.comp_add, ιTensorObj_tensorCochain_extend, extendCochain_add,
    MonoidalPreadditive.tensor_add, Preadditive.add_comp]

private lemma tensorCochain_smul_left {p q : ℕ} (r : k) (φ : A.X p ⟶ M) (ψ : B.X q ⟶ N)
    (n : ℕ) : tensorCochain μ (r • φ) ψ n = r • tensorCochain μ φ ψ n := by
  refine mapBifunctor.hom_ext fun i j (h : i + j = n) ↦ ?_
  change ιTensorObj A B i j n h ≫ _ = ιTensorObj A B i j n h ≫ _
  simp only [Linear.comp_smul, ιTensorObj_tensorCochain_extend, extendCochain_smul,
    smul_tensorHom, Linear.smul_comp]

private lemma tensorCochain_smul_right {p q : ℕ} (r : k) (φ : A.X p ⟶ M) (ψ : B.X q ⟶ N)
    (n : ℕ) : tensorCochain μ φ (r • ψ) n = r • tensorCochain μ φ ψ n := by
  refine mapBifunctor.hom_ext fun i j (h : i + j = n) ↦ ?_
  change ιTensorObj A B i j n h ≫ _ = ιTensorObj A B i j n h ≫ _
  simp only [Linear.comp_smul, ιTensorObj_tensorCochain_extend, extendCochain_smul,
    tensorHom_smul, Linear.smul_comp]

end Tensor

section Cochain

variable {k : Type*} [CommRing k] [Linear k C] [MonoidalLinear k C] (D : E ⟶ A ⊗ B)
  (μ : M ⊗ N ⟶ P)

variable (k) in
/-- **The cup product of cochains** along the diagonal `D : E ⟶ A ⊗ B`: for `p + q = n`, the
`k`-bilinear map sending cochains `φ : A_p ⟶ M` and `ψ : B_q ⟶ N` to the cochain
`E_n ⟶ (A ⊗ B)_n ⟶ P`, the component of `D` followed by the tensor product of cochains
`TauCeti.ChainComplex.tensorCochain`, which projects to `A_p ⊗ B_q` and applies `φ ⊗ ψ` and `μ`. -/
def cupCochain (p q n : ℕ) (_ : p + q = n) :
    (A.linearYonedaObj k M).X p →ₗ[k] (B.linearYonedaObj k N).X q →ₗ[k]
      (E.linearYonedaObj k P).X n :=
  LinearMap.mk₂ k (fun (φ : A.X p ⟶ M) (ψ : B.X q ⟶ N) ↦ D.f n ≫ tensorCochain μ φ ψ n)
    -- the module operations on `(A.linearYonedaObj k M).X p` are those of `A.X p ⟶ M`
    (fun φ φ' ψ ↦ (congrArg (D.f n ≫ ·) (tensorCochain_add_left μ φ φ' ψ n)).trans
      (Preadditive.comp_add _ _ _ _ _ _))
    (fun r φ ψ ↦ (congrArg (D.f n ≫ ·) (tensorCochain_smul_left μ r φ ψ n)).trans
      (Linear.comp_smul _ _ _ _ _ _))
    (fun φ ψ ψ' ↦ (congrArg (D.f n ≫ ·) (tensorCochain_add_right μ φ ψ ψ' n)).trans
      (Preadditive.comp_add _ _ _ _ _ _))
    (fun r φ ψ ↦ (congrArg (D.f n ≫ ·) (tensorCochain_smul_right μ r φ ψ n)).trans
      (Linear.comp_smul _ _ _ _ _ _))

/-- The cup product of cochains is the component of the diagonal followed by the tensor product of
cochains. -/
lemma cupCochain_apply (p q n : ℕ) (h : p + q = n) (φ : A.X p ⟶ M) (ψ : B.X q ⟶ N) :
    cupCochain k D μ p q n h φ ψ = D.f n ≫ tensorCochain μ φ ψ n :=
  LinearMap.mk₂_apply ..

/-- **The Leibniz rule for the cup product**: `(φ ⌣ ψ) ∘ d = (φ ∘ d) ⌣ ψ + (-1)^p φ ⌣ (ψ ∘ d)`
for a cochain `φ` of degree `p`. -/
lemma d_comp_cupCochain (p q n : ℕ) (h : p + q = n) (φ : A.X p ⟶ M) (ψ : B.X q ⟶ N) :
    E.d (n + 1) n ≫ cupCochain k D μ p q n h φ ψ =
      cupCochain k D μ (p + 1) q (n + 1) (by omega) (A.d (p + 1) p ≫ φ) ψ +
        ((-1 : ℤ) ^ p) • cupCochain k D μ p (q + 1) (n + 1) (by omega) φ (B.d (q + 1) q ≫ ψ) := by
  rw [cupCochain_apply, cupCochain_apply, cupCochain_apply, ← D.comm_assoc,
    d_comp_tensorCochain, Preadditive.comp_add, Preadditive.comp_zsmul]
  -- the `ℤ`-action on `(E.linearYonedaObj k P).X (n + 1)` is the one on `E.X (n + 1) ⟶ P`
  rfl

/-- **Naturality of the cup product of cochains** along a map of diagonals: if chain maps
`e : E' ⟶ E`, `f : A' ⟶ A` and `g : B' ⟶ B` satisfy `e ≫ D = D' ≫ (f ⊗ g)`, then cupping the
pulled-back cochains along `D'` is pulling back their cup product along `D`. -/
lemma cupCochain_naturality {A' B' E' : ChainComplex C ℕ} (D' : E' ⟶ A' ⊗ B') (e : E' ⟶ E)
    (f : A' ⟶ A) (g : B' ⟶ B) (hD : e ≫ D = D' ≫ (f ⊗ₘ g)) (p q n : ℕ) (h : p + q = n)
    (φ : A.X p ⟶ M) (ψ : B.X q ⟶ N) :
    cupCochain k D' μ p q n h (f.f p ≫ φ) (g.f q ≫ ψ) = e.f n ≫ cupCochain k D μ p q n h φ ψ := by
  rw [cupCochain_apply, cupCochain_apply, ← tensorHom_f_comp_tensorCochain, ← Category.assoc,
    ← HomologicalComplex.comp_f, ← hD, HomologicalComplex.comp_f, Category.assoc]

end Cochain

section Cohomology

variable {k : Type*} [CommRing k] [Linear k C] [MonoidalLinear k C] (D : E ⟶ A ⊗ B)
  (μ : M ⊗ N ⟶ P)

omit [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C] in
private lemma iCycles_injective (K : CochainComplex (ModuleCat k) ℕ) (n : ℕ) :
    Function.Injective (K.iCycles n) :=
  (ModuleCat.mono_iff_injective _).1 inferInstance

omit [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C] in
/-- A cocycle `φ` of `Hom(A, M)` satisfies `φ ∘ d = 0`, with `0` the zero of the module
`(A.linearYonedaObj k M).X (p + 1)`. -/
private lemma d_comp_iCycles {p : ℕ} (a : (A.linearYonedaObj k M).cycles p) :
    A.d (p + 1) p ≫ (A.linearYonedaObj k M).iCycles p a =
      (0 : (A.linearYonedaObj k M).X (p + 1)) :=
  ConcreteCategory.congr_hom ((A.linearYonedaObj k M).iCycles_d p (p + 1)) a

variable (k) in
/-- Cupping on the left with a fixed cocycle, as a map of cocycles. -/
private def cupCyclesLeft (p q n : ℕ) (h : p + q = n) (a : (A.linearYonedaObj k M).cycles p) :
    (B.linearYonedaObj k N).cycles q ⟶ (E.linearYonedaObj k P).cycles n :=
  (E.linearYonedaObj k P).liftCycles
    (ModuleCat.ofHom ((cupCochain k D μ p q n h ((A.linearYonedaObj k M).iCycles p a)) ∘ₗ
      ((B.linearYonedaObj k N).iCycles q).hom)) (n + 1) (by simp) (by
        ext b
        have := d_comp_cupCochain (k := k) D μ p q n h ((A.linearYonedaObj k M).iCycles p a)
          ((B.linearYonedaObj k N).iCycles q b)
        rw [d_comp_iCycles, d_comp_iCycles, LinearMap.map_zero₂, map_zero, smul_zero,
          add_zero] at this
        exact this)

private lemma iCycles_cupCyclesLeft (p q n : ℕ) (h : p + q = n)
    (a : (A.linearYonedaObj k M).cycles p) (b : (B.linearYonedaObj k N).cycles q) :
    (E.linearYonedaObj k P).iCycles n (cupCyclesLeft k D μ p q n h a b) =
      cupCochain k D μ p q n h ((A.linearYonedaObj k M).iCycles p a)
        ((B.linearYonedaObj k N).iCycles q b) :=
  ConcreteCategory.congr_hom ((E.linearYonedaObj k P).liftCycles_i _ _ _ _) b

variable (k) in
/-- **The cup product of cocycles**: the cup product `TauCeti.ChainComplex.cupCochain` of the
underlying cochains, which is a cocycle by the Leibniz rule
(`TauCeti.ChainComplex.iCycles_cupCycles`). -/
def cupCycles (p q n : ℕ) (h : p + q = n) :
    (A.linearYonedaObj k M).cycles p →ₗ[k] (B.linearYonedaObj k N).cycles q →ₗ[k]
      (E.linearYonedaObj k P).cycles n where
  toFun a := (cupCyclesLeft k D μ p q n h a).hom
  map_add' a a' := by
    ext b
    apply iCycles_injective
    simp [iCycles_cupCyclesLeft]
  map_smul' r a := by
    ext b
    apply iCycles_injective
    simp [iCycles_cupCyclesLeft]

/-- On underlying cochains, the cup product of cocycles is the cup product of cochains. -/
lemma iCycles_cupCycles (p q n : ℕ) (h : p + q = n) (a : (A.linearYonedaObj k M).cycles p)
    (b : (B.linearYonedaObj k N).cycles q) :
    (E.linearYonedaObj k P).iCycles n (cupCycles k D μ p q n h a b) =
      cupCochain k D μ p q n h ((A.linearYonedaObj k M).iCycles p a)
        ((B.linearYonedaObj k N).iCycles q b) :=
  iCycles_cupCyclesLeft D μ p q n h a b

omit [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C] in
private lemma linearYonedaObj_d_apply (K : ChainComplex C ℕ) (i j : ℕ)
    (x : (K.linearYonedaObj k M).X i) :
    (K.linearYonedaObj k M).d i j x = K.d j i ≫ x :=
  rfl

omit [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C] in
private lemma iCycles_toCycles_apply (K : CochainComplex (ModuleCat k) ℕ) (i j : ℕ) (x : K.X i) :
    K.iCycles j (K.toCycles i j x) = K.d i j x :=
  ConcreteCategory.congr_hom (K.toCycles_i i j) x

omit [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C] in
private lemma homologyπ_toCycles_apply (K : CochainComplex (ModuleCat k) ℕ) (i j : ℕ)
    (x : K.X i) : K.homologyπ j (K.toCycles i j x) = 0 :=
  ConcreteCategory.congr_hom (K.toCycles_comp_homologyπ i j) x

/-- A cocycle cupped with a coboundary is a coboundary. -/
private lemma homologyπ_cupCycles_toCycles_right (p q n : ℕ) (h : p + q = n)
    (a : (A.linearYonedaObj k M).cycles p) (i : ℕ) (x : (B.linearYonedaObj k N).X i) :
    (E.linearYonedaObj k P).homologyπ n
      (cupCycles k D μ p q n h a ((B.linearYonedaObj k N).toCycles i q x)) = 0 := by
  by_cases hiq : (ComplexShape.up ℕ).Rel i q
  · obtain rfl : i + 1 = q := hiq
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨p + i, by omega⟩
    -- by the Leibniz rule, `a ⌣ d x = (-1)^p d (a ⌣ x)`
    have key : cupCycles k D μ p (i + 1) (m + 1) h a
        ((B.linearYonedaObj k N).toCycles i (i + 1) x) =
        ((-1 : ℤ) ^ p) • (E.linearYonedaObj k P).toCycles m (m + 1)
          (cupCochain k D μ p i m (by omega) ((A.linearYonedaObj k M).iCycles p a) x) := by
      have hd := d_comp_cupCochain (k := k) D μ p i m (by omega)
        ((A.linearYonedaObj k M).iCycles p a) x
      rw [d_comp_iCycles, LinearMap.map_zero₂, zero_add] at hd
      apply iCycles_injective
      rw [iCycles_cupCycles, map_zsmul, iCycles_toCycles_apply, iCycles_toCycles_apply,
        linearYonedaObj_d_apply, linearYonedaObj_d_apply, hd, smul_smul, ← mul_pow, neg_one_mul,
        neg_neg, one_pow, one_smul]
    rw [key, map_zsmul, homologyπ_toCycles_apply, smul_zero]
  · rw [(B.linearYonedaObj k N).toCycles_eq_zero hiq]
    simp

/-- A coboundary cupped with a cocycle is a coboundary. -/
private lemma homologyπ_cupCycles_toCycles_left (p q n : ℕ) (h : p + q = n) (i : ℕ)
    (x : (A.linearYonedaObj k M).X i) (b : (B.linearYonedaObj k N).cycles q) :
    (E.linearYonedaObj k P).homologyπ n
      (cupCycles k D μ p q n h ((A.linearYonedaObj k M).toCycles i p x) b) = 0 := by
  by_cases hip : (ComplexShape.up ℕ).Rel i p
  · obtain rfl : i + 1 = p := hip
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨i + q, by omega⟩
    -- by the Leibniz rule, `d x ⌣ b = d (x ⌣ b)`
    have key : cupCycles k D μ (i + 1) q (m + 1) h
        ((A.linearYonedaObj k M).toCycles i (i + 1) x) b =
        (E.linearYonedaObj k P).toCycles m (m + 1)
          (cupCochain k D μ i q m (by omega) x ((B.linearYonedaObj k N).iCycles q b)) := by
      have hd := d_comp_cupCochain (k := k) D μ i q m (by omega) x
        ((B.linearYonedaObj k N).iCycles q b)
      rw [d_comp_iCycles, map_zero, smul_zero, add_zero] at hd
      apply iCycles_injective
      rw [iCycles_cupCycles, iCycles_toCycles_apply, iCycles_toCycles_apply,
        linearYonedaObj_d_apply, linearYonedaObj_d_apply, hd]
    rw [key, homologyπ_toCycles_apply]
  · rw [(A.linearYonedaObj k M).toCycles_eq_zero hip]
    simp

omit [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C] in
private lemma homologyπ_surjective (K : CochainComplex (ModuleCat k) ℕ) (n : ℕ) :
    Function.Surjective (K.homologyπ n) :=
  (ModuleCat.epi_iff_surjective _).1 inferInstance

variable (k) in
/-- Cupping on the left with a fixed cocycle, on cohomology. -/
private def cupHomologyLeft (p q n : ℕ) (h : p + q = n) (a : (A.linearYonedaObj k M).cycles p) :
    (B.linearYonedaObj k N).homology q ⟶ (E.linearYonedaObj k P).homology n :=
  (CokernelCofork.IsColimit.desc' ((B.linearYonedaObj k N).homologyIsCokernel _ q rfl)
    (ModuleCat.ofHom (cupCycles k D μ p q n h a) ≫ (E.linearYonedaObj k P).homologyπ n)
    (by
      ext x
      exact homologyπ_cupCycles_toCycles_right D μ p q n h a _ x)).1

private lemma cupHomologyLeft_homologyπ (p q n : ℕ) (h : p + q = n)
    (a : (A.linearYonedaObj k M).cycles p) (b : (B.linearYonedaObj k N).cycles q) :
    (cupHomologyLeft k D μ p q n h a).hom ((B.linearYonedaObj k N).homologyπ q b) =
      (E.linearYonedaObj k P).homologyπ n (cupCycles k D μ p q n h a b) := by
  unfold cupHomologyLeft
  exact ConcreteCategory.congr_hom (CokernelCofork.IsColimit.desc'
    ((B.linearYonedaObj k N).homologyIsCokernel _ q rfl)
    (ModuleCat.ofHom (cupCycles k D μ p q n h a) ≫ (E.linearYonedaObj k P).homologyπ n) _).2 b

variable (k) in
/-- Cupping with a fixed cocycle on the left, as a linear function of that cocycle. -/
private def cupCyclesHomology (p q n : ℕ) (h : p + q = n) :
    (A.linearYonedaObj k M).cycles p ⟶
      ModuleCat.of k
        ((B.linearYonedaObj k N).homology q →ₗ[k] (E.linearYonedaObj k P).homology n) :=
  ModuleCat.ofHom (X := (A.linearYonedaObj k M).cycles p)
    { toFun a := (cupHomologyLeft k D μ p q n h a).hom
      map_add' a a' := LinearMap.ext fun β ↦ by
        obtain ⟨b, rfl⟩ := homologyπ_surjective _ q β
        simp only [cupHomologyLeft_homologyπ, map_add, LinearMap.add_apply]
      map_smul' r a := LinearMap.ext fun β ↦ by
        obtain ⟨b, rfl⟩ := homologyπ_surjective _ q β
        simp only [cupHomologyLeft_homologyπ, LinearMap.smul_apply, RingHom.id_apply]
        rw [map_smul, LinearMap.smul_apply, map_smul] }

private lemma toCycles_comp_cupCyclesHomology (p q n : ℕ) (h : p + q = n) :
    (A.linearYonedaObj k M).toCycles ((ComplexShape.up ℕ).prev p) p ≫
      cupCyclesHomology k D μ p q n h = 0 := by
  ext x : 2
  refine LinearMap.ext fun β ↦ ?_
  obtain ⟨b, rfl⟩ := homologyπ_surjective _ q β
  exact (cupHomologyLeft_homologyπ D μ p q n h _ b).trans
    (homologyπ_cupCycles_toCycles_left D μ p q n h _ x b)

variable (k) in
/-- **The cup product on cohomology**, `Hᵖ(Hom(A, M)) × H^q(Hom(B, N)) ⟶ Hⁿ(Hom(E, P))` for
`p + q = n`, along the diagonal `D : E ⟶ A ⊗ B` and the pairing `μ : M ⊗ N ⟶ P`: the class of
`a ⌣ b` on the classes of cocycles `a` and `b` (`TauCeti.ChainComplex.cup_homologyπ`). -/
def cup (p q n : ℕ) (h : p + q = n) :
    (A.linearYonedaObj k M).homology p →ₗ[k] (B.linearYonedaObj k N).homology q →ₗ[k]
      (E.linearYonedaObj k P).homology n :=
  (CokernelCofork.IsColimit.desc' ((A.linearYonedaObj k M).homologyIsCokernel _ p rfl)
    (cupCyclesHomology k D μ p q n h) (toCycles_comp_cupCyclesHomology D μ p q n h)).1.hom

/-- **The cup product on classes**: the cup product of the classes of two cocycles is the class of
their cup product. -/
@[simp]
lemma cup_homologyπ (p q n : ℕ) (h : p + q = n) (a : (A.linearYonedaObj k M).cycles p)
    (b : (B.linearYonedaObj k N).cycles q) :
    cup k D μ p q n h ((A.linearYonedaObj k M).homologyπ p a)
        ((B.linearYonedaObj k N).homologyπ q b) =
      (E.linearYonedaObj k P).homologyπ n (cupCycles k D μ p q n h a b) := by
  have hfac := ConcreteCategory.congr_hom (CokernelCofork.IsColimit.desc'
    ((A.linearYonedaObj k M).homologyIsCokernel _ p rfl) (cupCyclesHomology k D μ p q n h)
    (toCycles_comp_cupCyclesHomology D μ p q n h)).2 a
  rw [cup, ← cupHomologyLeft_homologyπ]
  exact congrArg (fun F : (B.linearYonedaObj k N).homology q →ₗ[k]
    (E.linearYonedaObj k P).homology n ↦ F ((B.linearYonedaObj k N).homologyπ q b)) hfac

omit [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C] in
private lemma homologyMap_homologyπ_apply {A' : ChainComplex C ℕ} (f : A' ⟶ A) (n : ℕ)
    (x : (A.linearYonedaObj k M).cycles n) :
    homologyMap (K := A.linearYonedaObj k M) (L := A'.linearYonedaObj k M)
        ((linearYonedaFunctor k M).map f.op) n ((A.linearYonedaObj k M).homologyπ n x) =
      (A'.linearYonedaObj k M).homologyπ n
        (cyclesMap (K := A.linearYonedaObj k M) (L := A'.linearYonedaObj k M)
          ((linearYonedaFunctor k M).map f.op) n x) :=
  ConcreteCategory.congr_hom (homologyπ_naturality _ n) x

omit [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C] in
private lemma iCycles_cyclesMap_apply {A' : ChainComplex C ℕ} (f : A' ⟶ A) (n : ℕ)
    (x : (A.linearYonedaObj k M).cycles n) :
    (A'.linearYonedaObj k M).iCycles n
        (cyclesMap (K := A.linearYonedaObj k M) (L := A'.linearYonedaObj k M)
          ((linearYonedaFunctor k M).map f.op) n x) =
      f.f n ≫ (A.linearYonedaObj k M).iCycles n x :=
  ConcreteCategory.congr_hom (cyclesMap_i _ n) x

/-- **Naturality of the cup product on cohomology** along a map of diagonals: if chain maps
`e : E' ⟶ E`, `f : A' ⟶ A` and `g : B' ⟶ B` satisfy `e ≫ D = D' ≫ (f ⊗ g)`, then the cup product
along `D'` of the pulled-back classes is the pull-back of the cup product along `D`. -/
lemma cup_naturality {A' B' E' : ChainComplex C ℕ} (D' : E' ⟶ A' ⊗ B') (e : E' ⟶ E)
    (f : A' ⟶ A) (g : B' ⟶ B) (hD : e ≫ D = D' ≫ (f ⊗ₘ g)) (p q n : ℕ) (h : p + q = n)
    (α : (A.linearYonedaObj k M).homology p) (β : (B.linearYonedaObj k N).homology q) :
    cup k D' μ p q n h
        (homologyMap (K := A.linearYonedaObj k M) (L := A'.linearYonedaObj k M)
          ((linearYonedaFunctor k M).map f.op) p α)
        (homologyMap (K := B.linearYonedaObj k N) (L := B'.linearYonedaObj k N)
          ((linearYonedaFunctor k N).map g.op) q β) =
      homologyMap (K := E.linearYonedaObj k P) (L := E'.linearYonedaObj k P)
        ((linearYonedaFunctor k P).map e.op) n (cup k D μ p q n h α β) := by
  obtain ⟨a, rfl⟩ := homologyπ_surjective _ p α
  obtain ⟨b, rfl⟩ := homologyπ_surjective _ q β
  rw [homologyMap_homologyπ_apply, homologyMap_homologyπ_apply, cup_homologyπ, cup_homologyπ,
    homologyMap_homologyπ_apply]
  congr 1
  apply iCycles_injective
  rw [iCycles_cupCycles, iCycles_cyclesMap_apply, iCycles_cyclesMap_apply, iCycles_cyclesMap_apply,
    iCycles_cupCycles]
  exact cupCochain_naturality D μ D' e f g hD p q n h _ _

end Cohomology

end TauCeti.ChainComplex
