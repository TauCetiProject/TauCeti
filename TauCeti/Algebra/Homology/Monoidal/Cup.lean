/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.LinearYoneda
public import TauCeti.Algebra.Homology.ModuleCat
public import TauCeti.Algebra.Homology.Monoidal.TensorCochain

/-!
# Cup products of cochains along a diagonal

Let `C` be a `k`-linear preadditive monoidal category, let `A`, `B` and `E` be chain complexes in
`C` indexed by `ℕ` such that the tensor product `A ⊗ B` exists, and let `D : E ⟶ A ⊗ B` be a chain
map, a *diagonal*.
Given a pairing `μ : M ⊗ N ⟶ P` of coefficient objects, a cochain `φ : A_p ⟶ M` and a cochain
`ψ : B_q ⟶ N` have the cup product `φ ⌣ ψ : E_n ⟶ P`, for `p + q = n`: the degree-`n` component
of `D`, followed by the projection of `(A ⊗ B)_n` onto its summand `A_p ⊗ B_q`, by `φ ⊗ ψ` and by
`μ`.  Since `D` is a chain map and the tensor product carries the Koszul signs, it satisfies the
Leibniz rule `(φ ⌣ ψ) ∘ d = (φ ∘ d) ⌣ ψ + (-1)^p φ ⌣ (ψ ∘ d)`.  When `C` is moreover abelian, a
cocycle cupped with a cocycle is a cocycle, a coboundary cupped with a cocycle (in either order)
is a coboundary, and the cup product descends to a `k`-bilinear map
`Hᵖ(Hom(A, M)) × H^q(Hom(B, N)) ⟶ Hⁿ(Hom(E, P))` on the cohomology of the complexes
`ChainComplex.linearYonedaObj`.  It is natural along maps of diagonals.

The singular cup product is the case where `D` is the Alexander–Whitney map precomposed with the
diagonal of a space; there `φ ⌣ ψ` evaluates a singular simplex on its front `p`-face and its back
`q`-face.

## Main definitions and results

* `TauCeti.ChainComplex.cupCochain`: the cup product of cochains.
* `TauCeti.ChainComplex.d_comp_cupCochain`: the Leibniz rule.
* `TauCeti.ChainComplex.cupCochain_naturality`: naturality along a map of diagonals.
* `TauCeti.ChainComplex.cupCycles`: the cup product of cocycles.
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

variable {C : Type*} [Category* C]

section Cochain

variable [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C] {A B E : ChainComplex C ℕ}
  [A.HasTensor B] {M N P : C} {k : Type*} [CommSemiring k] [Linear k C] [MonoidalLinear k C]
  (D : E ⟶ HomologicalComplex.tensorObj A B) (μ : M ⊗ N ⟶ P)

variable (k) in
/-- **The cup product of cochains** along the diagonal `D : E ⟶ A ⊗ B`: for `p + q = n`, the
`k`-bilinear map sending cochains `φ : A_p ⟶ M` and `ψ : B_q ⟶ N` to the cochain
`E_n ⟶ (A ⊗ B)_n ⟶ P`, the component of `D` followed by the tensor product of cochains
`TauCeti.ChainComplex.tensorCochain`, which projects to `A_p ⊗ B_q` and applies `φ ⊗ ψ` and `μ`. -/
def cupCochain (p q n : ℕ) (_ : p + q = n) :
    (A.X p ⟶ M) →ₗ[k] (B.X q ⟶ N) →ₗ[k] (E.X n ⟶ P) :=
  LinearMap.mk₂ k (fun (φ : A.X p ⟶ M) (ψ : B.X q ⟶ N) ↦ D.f n ≫ tensorCochain μ φ ψ n)
    (fun φ φ' ψ ↦ by rw [tensorCochain_add_left, Preadditive.comp_add])
    (fun r φ ψ ↦ by rw [tensorCochain_smul_left, Linear.comp_smul])
    (fun φ ψ ψ' ↦ by rw [tensorCochain_add_right, Preadditive.comp_add])
    (fun r φ ψ ↦ by rw [tensorCochain_smul_right, Linear.comp_smul])

/-- The cup product of cochains is the component of the diagonal followed by the tensor product of
cochains. -/
@[simp]
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

/-- **Naturality of the cup product of cochains** along a map of diagonals: if chain maps
`e : E' ⟶ E`, `f : A' ⟶ A` and `g : B' ⟶ B` satisfy `e ≫ D = D' ≫ (f ⊗ g)`, then cupping the
pulled-back cochains along `D'` is pulling back their cup product along `D`. -/
lemma cupCochain_naturality {A' B' E' : ChainComplex C ℕ} [A'.HasTensor B']
    (D' : E' ⟶ HomologicalComplex.tensorObj A' B') (e : E' ⟶ E) (f : A' ⟶ A) (g : B' ⟶ B)
    (hD : e ≫ D = D' ≫ HomologicalComplex.tensorHom f g) (p q n : ℕ) (h : p + q = n)
    (φ : A.X p ⟶ M) (ψ : B.X q ⟶ N) :
    cupCochain k D' μ p q n h (f.f p ≫ φ) (g.f q ≫ ψ) = e.f n ≫ cupCochain k D μ p q n h φ ψ := by
  rw [cupCochain_apply, cupCochain_apply, ← tensorHom_f_comp_tensorCochain, ← Category.assoc,
    ← HomologicalComplex.comp_f, ← hD, HomologicalComplex.comp_f, Category.assoc]

end Cochain

section Cohomology

variable [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C] {A B E : ChainComplex C ℕ}
  [A.HasTensor B] {M N P : C} {k : Type*} [CommRing k] [Linear k C] [MonoidalLinear k C]
  (D : E ⟶ HomologicalComplex.tensorObj A B) (μ : M ⊗ N ⟶ P)

variable (k) in
/-- The cup product of cochains `TauCeti.ChainComplex.cupCochain`, as a bilinear map of the
cochain modules of the complexes `Hom(-, -)`. -/
private def cupCochainHom (p q n : ℕ) (h : p + q = n) :
    (A.linearYonedaObj k M).X p →ₗ[k] (B.linearYonedaObj k N).X q →ₗ[k]
      (E.linearYonedaObj k P).X n :=
  cupCochain k D μ p q n h

/-- The Leibniz rule `TauCeti.ChainComplex.d_comp_cupCochain` in the cochain modules of the
complexes `Hom(-, -)`. -/
private lemma d_comp_cupCochainHom (p q n : ℕ) (h : p + q = n) (φ : (A.linearYonedaObj k M).X p)
    (ψ : (B.linearYonedaObj k N).X q) :
    E.d (n + 1) n ≫ cupCochainHom k D μ p q n h φ ψ =
      cupCochainHom k D μ (p + 1) q (n + 1) (by omega) (A.d (p + 1) p ≫ φ) ψ +
        ((-1 : ℤ) ^ p) • cupCochainHom k D μ p (q + 1) (n + 1) (by omega) φ (B.d (q + 1) q ≫ ψ) :=
  d_comp_cupCochain D μ p q n h φ ψ

variable (k) in
/-- Cupping on the left with a fixed cocycle, as a map of cocycles. -/
private def cupCyclesLeft (p q n : ℕ) (h : p + q = n) (a : (A.linearYonedaObj k M).cycles p) :
    (B.linearYonedaObj k N).cycles q ⟶ (E.linearYonedaObj k P).cycles n :=
  (E.linearYonedaObj k P).liftCycles
    (ModuleCat.ofHom ((cupCochainHom k D μ p q n h ((A.linearYonedaObj k M).iCycles p a)) ∘ₗ
      ((B.linearYonedaObj k N).iCycles q).hom)) (n + 1) (by simp) (by
        ext b
        have := d_comp_cupCochainHom (k := k) D μ p q n h ((A.linearYonedaObj k M).iCycles p a)
          ((B.linearYonedaObj k N).iCycles q b)
        rw [d_comp_linearYonedaObj_iCycles, d_comp_linearYonedaObj_iCycles, LinearMap.map_zero₂,
          map_zero, smul_zero, add_zero] at this
        exact this)

private lemma iCycles_cupCyclesLeft (p q n : ℕ) (h : p + q = n)
    (a : (A.linearYonedaObj k M).cycles p) (b : (B.linearYonedaObj k N).cycles q) :
    (E.linearYonedaObj k P).iCycles n (cupCyclesLeft k D μ p q n h a b) =
      cupCochainHom k D μ p q n h ((A.linearYonedaObj k M).iCycles p a)
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
    apply HomologicalComplex.moduleCat_iCycles_injective
    simp [iCycles_cupCyclesLeft]
  map_smul' r a := by
    ext b
    apply HomologicalComplex.moduleCat_iCycles_injective
    simp [iCycles_cupCyclesLeft]

/-- On underlying cochains, the cup product of cocycles is the cup product of cochains. -/
@[simp]
lemma iCycles_cupCycles (p q n : ℕ) (h : p + q = n) (a : (A.linearYonedaObj k M).cycles p)
    (b : (B.linearYonedaObj k N).cycles q) :
    (E.linearYonedaObj k P).iCycles n (cupCycles k D μ p q n h a b) =
      cupCochain k D μ p q n h ((A.linearYonedaObj k M).iCycles p a)
        ((B.linearYonedaObj k N).iCycles q b) :=
  iCycles_cupCyclesLeft D μ p q n h a b

private lemma iCycles_cupCycles_cupCochainHom (p q n : ℕ) (h : p + q = n)
    (a : (A.linearYonedaObj k M).cycles p) (b : (B.linearYonedaObj k N).cycles q) :
    (E.linearYonedaObj k P).iCycles n (cupCycles k D μ p q n h a b) =
      cupCochainHom k D μ p q n h ((A.linearYonedaObj k M).iCycles p a)
        ((B.linearYonedaObj k N).iCycles q b) :=
  iCycles_cupCyclesLeft D μ p q n h a b

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
          (cupCochainHom k D μ p i m (by omega) ((A.linearYonedaObj k M).iCycles p a) x) := by
      have hd := d_comp_cupCochainHom (k := k) D μ p i m (by omega)
        ((A.linearYonedaObj k M).iCycles p a) x
      rw [d_comp_linearYonedaObj_iCycles, LinearMap.map_zero₂, zero_add] at hd
      apply HomologicalComplex.moduleCat_iCycles_injective
      rw [iCycles_cupCycles_cupCochainHom, map_zsmul, linearYonedaObj_iCycles_toCycles_apply,
        linearYonedaObj_iCycles_toCycles_apply, hd, smul_smul, ← mul_pow, neg_one_mul, neg_neg,
        one_pow, one_smul]
    rw [key, map_zsmul, linearYonedaObj_homologyπ_toCycles_apply, smul_zero]
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
          (cupCochainHom k D μ i q m (by omega) x ((B.linearYonedaObj k N).iCycles q b)) := by
      have hd := d_comp_cupCochainHom (k := k) D μ i q m (by omega) x
        ((B.linearYonedaObj k N).iCycles q b)
      rw [d_comp_linearYonedaObj_iCycles, map_zero, smul_zero, add_zero] at hd
      apply HomologicalComplex.moduleCat_iCycles_injective
      rw [iCycles_cupCycles_cupCochainHom, linearYonedaObj_iCycles_toCycles_apply,
        linearYonedaObj_iCycles_toCycles_apply, hd]
    rw [key, linearYonedaObj_homologyπ_toCycles_apply]
  · rw [(A.linearYonedaObj k M).toCycles_eq_zero hip]
    simp

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
        obtain ⟨b, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ q β
        simp only [cupHomologyLeft_homologyπ, map_add, LinearMap.add_apply]
      map_smul' r a := LinearMap.ext fun β ↦ by
        obtain ⟨b, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ q β
        simp only [cupHomologyLeft_homologyπ, LinearMap.smul_apply, RingHom.id_apply]
        rw [map_smul, LinearMap.smul_apply, map_smul] }

private lemma toCycles_comp_cupCyclesHomology (p q n : ℕ) (h : p + q = n) :
    (A.linearYonedaObj k M).toCycles ((ComplexShape.up ℕ).prev p) p ≫
      cupCyclesHomology k D μ p q n h = 0 := by
  ext x : 2
  refine LinearMap.ext fun β ↦ ?_
  obtain ⟨b, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ q β
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
  exact LinearMap.congr_fun hfac _

/-- **Naturality of the cup product on cohomology** along a map of diagonals: if chain maps
`e : E' ⟶ E`, `f : A' ⟶ A` and `g : B' ⟶ B` satisfy `e ≫ D = D' ≫ (f ⊗ g)`, then the cup product
along `D'` of the pulled-back classes is the pull-back of the cup product along `D`. -/
lemma cup_naturality {A' B' E' : ChainComplex C ℕ} [A'.HasTensor B']
    (D' : E' ⟶ HomologicalComplex.tensorObj A' B') (e : E' ⟶ E) (f : A' ⟶ A) (g : B' ⟶ B)
    (hD : e ≫ D = D' ≫ HomologicalComplex.tensorHom f g) (p q n : ℕ) (h : p + q = n)
    (α : (A.linearYonedaObj k M).homology p) (β : (B.linearYonedaObj k N).homology q) :
    cup k D' μ p q n h
        (homologyMap (K := A.linearYonedaObj k M) (L := A'.linearYonedaObj k M)
          ((linearYonedaFunctor k M).map f.op) p α)
        (homologyMap (K := B.linearYonedaObj k N) (L := B'.linearYonedaObj k N)
          ((linearYonedaFunctor k N).map g.op) q β) =
      homologyMap (K := E.linearYonedaObj k P) (L := E'.linearYonedaObj k P)
        ((linearYonedaFunctor k P).map e.op) n (cup k D μ p q n h α β) := by
  obtain ⟨a, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p α
  obtain ⟨b, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ q β
  rw [homologyMap_linearYonedaFunctor_map_homologyπ_apply,
    homologyMap_linearYonedaFunctor_map_homologyπ_apply, cup_homologyπ, cup_homologyπ,
    homologyMap_linearYonedaFunctor_map_homologyπ_apply]
  congr 1
  apply HomologicalComplex.moduleCat_iCycles_injective
  rw [iCycles_cupCycles, iCycles_cyclesMap_linearYonedaFunctor_map_apply,
    iCycles_cyclesMap_linearYonedaFunctor_map_apply,
    iCycles_cyclesMap_linearYonedaFunctor_map_apply, iCycles_cupCycles]
  exact cupCochain_naturality D μ D' e f g hD p q n h _ _

end Cohomology

end TauCeti.ChainComplex
