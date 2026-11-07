/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Monoidal.TensorMk
public import TauCeti.Algebra.Homology.Kronecker
public import TauCeti.Algebra.Homology.Monoidal.Homology.Cross
public import TauCeti.Algebra.Homology.Monoidal.Tensor.Differential

/-!
# Slant products of cochains with chains

Let `K`, `L` and `T` be chain complexes of modules over a commutative ring `k`, indexed by `ℕ`,
and let `D : K ⊗ L ⟶ T` be a chain map, for instance the shuffle map
`C(X) ⊗ C(Y) ⟶ C(X × Y)` of singular chains. A chain `z ∈ K_p` and a cochain `φ : T_n ⟶ P`,
for `p + q = n`, have the **slant product** `φ / z : L_q ⟶ P`, the cochain

`(φ / z)(v) = φ (D (z ⊗ v))`.

Since `D` is a chain map and the tensor product carries the Koszul signs, the coboundary of the
slant product by a chain `z` of degree `p` is `δ(φ / z) = (-1)^p (δφ / z - φ / ∂z)`
(`TauCeti.ChainComplex.d_comp_slantCochain_zero`, `TauCeti.ChainComplex.slantCochain_d_comp_succ`
and `TauCeti.ChainComplex.slantCochain_d_zero`, which keep track of the degrees in `ℕ`).
Hence a cocycle slanted by a cycle is a cocycle, a coboundary slanted by a cycle is a coboundary,
and a cocycle slanted by a boundary is a coboundary, so the slant product descends to a
`k`-bilinear map

`Hₚ(K) × Hⁿ(Hom(T, P)) ⟶ H^q(Hom(L, P))`

(`TauCeti.ChainComplex.slant`). It satisfies the evaluation law
`⟨φ / x, y⟩ = ⟨φ, D_*(x × y)⟩` for homology classes `x ∈ Hₚ(K)` and `y ∈ H_q(L)`
(`TauCeti.ChainComplex.kronecker_slant`), where `x × y` is the homology cross product
`HomologicalComplex.homologyCross`, and it is natural along maps of the triples `(K, L, T)`
compatible with the chain maps `D` (`TauCeti.ChainComplex.slant_naturality`).

The slant product of singular cohomology, `Hⁿ(X × Y) × Hₚ(X) ⟶ H^q(Y)`, is the case where `D` is
the shuffle map; it produces, for instance, the classes `c₁(U) / γ ∈ H¹(Y)` of a line bundle `U`
on `X × Y` and loops `γ` in `X`.

## Main definitions and results

* `TauCeti.ChainComplex.slantCochain`: the slant product of a chain and a cochain.
* `TauCeti.ChainComplex.d_comp_slantCochain_zero`, `TauCeti.ChainComplex.slantCochain_d_comp_succ`
  and `TauCeti.ChainComplex.slantCochain_d_zero`: the boundary formulas.
* `TauCeti.ChainComplex.slantCycles`: the slant product of a cycle and a cocycle.
* `TauCeti.ChainComplex.slant`: the slant product on homology and cohomology, with
  `TauCeti.ChainComplex.slant_homologyπ` computing it on classes of cycles and cocycles.
* `TauCeti.ChainComplex.kronecker_slant`: the evaluation law `⟨φ / x, y⟩ = ⟨φ, D_*(x × y)⟩`.
* `TauCeti.ChainComplex.slant_naturality`: naturality.

## References

* E. H. Spanier, *Algebraic Topology*, McGraw–Hill, 1966, Chapter 6 (the slant product).
* A. Dold, *Lectures on Algebraic Topology*, Springer, 1972, Chapter VII (products).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex

universe u

namespace TauCeti.ChainComplex

variable {k : Type u} [CommRing k] {K L T : ChainComplex (ModuleCat.{u} k) ℕ} [K.HasTensor L]
  (D : HomologicalComplex.tensorObj K L ⟶ T) {P : ModuleCat.{u} k}

section Cochain

variable (k) in
/-- **The slant product of a chain and a cochain** along `D : K ⊗ L ⟶ T`: for `p + q = n`, the
`k`-bilinear map sending a chain `z ∈ K_p` and a cochain `φ : T_n ⟶ P` to the cochain
`v ↦ φ (D (z ⊗ v))` on `L_q` (`TauCeti.ChainComplex.slantCochain_apply`). -/
def slantCochain (p q n : ℕ) (h : p + q = n) : K.X p →ₗ[k] (T.X n ⟶ P) →ₗ[k] (L.X q ⟶ P) :=
  LinearMap.mk₂ k (fun z φ ↦ ModuleCat.tensorMk z ≫ ιTensorObj K L p q n h ≫ D.f n ≫ φ)
    (fun z z' φ ↦ by rw [ModuleCat.tensorMk_add, Preadditive.add_comp])
    (fun r z φ ↦ by rw [ModuleCat.tensorMk_smul, Linear.smul_comp])
    (fun z φ φ' ↦ by simp only [Preadditive.comp_add])
    (fun r z φ ↦ by simp only [Linear.comp_smul])

private lemma slantCochain_eq (p q n : ℕ) (h : p + q = n) (z : K.X p) (φ : T.X n ⟶ P) :
    slantCochain k D p q n h z φ = ModuleCat.tensorMk z ≫ ιTensorObj K L p q n h ≫ D.f n ≫ φ :=
  LinearMap.mk₂_apply ..

/-- The slant product `φ / z` evaluates `φ` on `D (z ⊗ v)`. -/
@[simp]
lemma slantCochain_apply (p q n : ℕ) (h : p + q = n) (z : K.X p) (φ : T.X n ⟶ P) (v : L.X q) :
    slantCochain k D p q n h z φ v = φ (D.f n (ιTensorObj K L p q n h (z ⊗ₜ v))) := by
  rw [slantCochain_eq]
  rfl

private lemma tensorObj_d_eq (n : ℕ) :
    (HomologicalComplex.tensorObj K L).d (n + 1) n =
      mapBifunctor.D₁ K L (curriedTensor _) (ComplexShape.down ℕ) (n + 1) n +
        mapBifunctor.D₂ K L (curriedTensor _) (ComplexShape.down ℕ) (n + 1) n :=
  mapBifunctor.d_eq _ _ _ _ _ _

/-- **The boundary formula for the slant product by a chain of degree zero**: the coboundary of
`φ / z` is `δφ / z`. -/
lemma d_comp_slantCochain_zero (q : ℕ) (z : K.X 0) (φ : T.X q ⟶ P) :
    L.d (q + 1) q ≫ slantCochain k D 0 q q (zero_add q) z φ =
      slantCochain k D 0 (q + 1) (q + 1) (zero_add _) z (T.d (q + 1) q ≫ φ) := by
  rw [slantCochain_eq, slantCochain_eq, D.comm_assoc, tensorObj_d_eq,
    ModuleCat.comp_tensorMk_assoc]
  simp only [Preadditive.add_comp, Preadditive.comp_add,
    ChainComplex.ιTensorObj_D₁_zero_assoc, ChainComplex.ιTensorObj_D₂_succ_assoc, zero_comp,
    zero_add, pow_zero, one_smul, Category.assoc]

/-- **The boundary formula for the slant product by a chain of positive degree**: for a chain
`w ∈ K_{p+1}` and a cochain `φ` of `T`, `δφ / w = φ / ∂w + (-1)^(p+1) δ(φ / w)`. -/
lemma slantCochain_d_comp_succ (p s n : ℕ) (h : p + 1 + s = n) (w : K.X (p + 1))
    (φ : T.X n ⟶ P) :
    slantCochain k D (p + 1) (s + 1) (n + 1) (by omega) w (T.d (n + 1) n ≫ φ) =
      slantCochain k D p (s + 1) n (by omega) (K.d (p + 1) p w) φ +
        ((-1 : ℤ) ^ (p + 1)) • (L.d (s + 1) s ≫ slantCochain k D (p + 1) s n h w φ) := by
  obtain rfl := h
  rw [slantCochain_eq, slantCochain_eq, slantCochain_eq, D.comm_assoc, tensorObj_d_eq]
  simp only [Preadditive.add_comp, Preadditive.comp_add,
    ChainComplex.ιTensorObj_D₁_succ_assoc, ChainComplex.ιTensorObj_D₂_succ_assoc,
    Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc,
    ModuleCat.tensorMk_whiskerRight_assoc, ModuleCat.comp_tensorMk_assoc]

/-- **The slant product by a boundary, in degree zero of `L`**: for a chain `w ∈ K_{p+1}`,
`φ / ∂w = δφ / w` on `L_0`. -/
lemma slantCochain_d_zero (p : ℕ) (w : K.X (p + 1)) (φ : T.X p ⟶ P) :
    slantCochain k D p 0 p (add_zero p) (K.d (p + 1) p w) φ =
      slantCochain k D (p + 1) 0 (p + 1) (add_zero _) w (T.d (p + 1) p ≫ φ) := by
  rw [slantCochain_eq, slantCochain_eq, D.comm_assoc, tensorObj_d_eq]
  simp only [Preadditive.add_comp, Preadditive.comp_add,
    ChainComplex.ιTensorObj_D₁_succ_assoc, ChainComplex.ιTensorObj_D₂_zero_assoc, zero_comp,
    add_zero, ModuleCat.tensorMk_whiskerRight_assoc]

/-- **Naturality of the slant product of chains and cochains**: if chain maps `f : K' ⟶ K`,
`g : L' ⟶ L` and `e : T' ⟶ T` satisfy `(f ⊗ g) ≫ D = D' ≫ e`, then slanting the pulled-back
cochain by `z` along `D'` is pulling back along `g` the slant by `f z` along `D`. -/
lemma slantCochain_naturality {K' L' T' : ChainComplex (ModuleCat.{u} k) ℕ} [K'.HasTensor L']
    (D' : HomologicalComplex.tensorObj K' L' ⟶ T') (f : K' ⟶ K) (g : L' ⟶ L) (e : T' ⟶ T)
    (hD : HomologicalComplex.tensorHom f g ≫ D = D' ≫ e) (p q n : ℕ) (h : p + q = n)
    (z : K'.X p) (φ : T.X n ⟶ P) :
    slantCochain k D' p q n h z (e.f n ≫ φ) = g.f q ≫ slantCochain k D p q n h (f.f p z) φ := by
  ext v
  have hD' := ConcreteCategory.congr_hom (congrArg (fun F ↦ F.f n) hD)
    (ιTensorObj K' L' p q n h (z ⊗ₜ v))
  simp only [HomologicalComplex.comp_f, ConcreteCategory.comp_apply] at hD'
  simp only [ConcreteCategory.comp_apply, slantCochain_apply, ← hD',
    HomologicalComplex.ι_tensorHom_apply]

end Cochain

section Cohomology

variable (k) in
/-- The slant product of chains and cochains `TauCeti.ChainComplex.slantCochain`, as a bilinear
map into the cochain modules of the complexes `Hom(-, -)`. The cochain module
`(L.linearYonedaObj k P).X q` agrees with `L.X q ⟶ P` only after unfolding `linearYonedaObj`, so
`rw` and `simp` with the `iCycles` and `toCycles` lemmas of `linearYonedaObj` match values of this
map but not values of `slantCochain`. -/
private def slantCochainHom (p q n : ℕ) (h : p + q = n) :
    K.X p →ₗ[k] (T.linearYonedaObj k P).X n →ₗ[k] (L.linearYonedaObj k P).X q :=
  slantCochain k D p q n h

private lemma d_comp_slantCochainHom_zero (q : ℕ) (z : K.X 0) (φ : (T.linearYonedaObj k P).X q) :
    L.d (q + 1) q ≫ slantCochainHom k D 0 q q (zero_add q) z φ =
      slantCochainHom k D 0 (q + 1) (q + 1) (zero_add _) z (T.d (q + 1) q ≫ φ) :=
  d_comp_slantCochain_zero D q z φ

private lemma slantCochainHom_d_comp_succ (p s n : ℕ) (h : p + 1 + s = n) (w : K.X (p + 1))
    (φ : (T.linearYonedaObj k P).X n) :
    ((-1 : ℤ) ^ (p + 1)) • (L.d (s + 1) s ≫ slantCochainHom k D (p + 1) s n h w φ) =
      slantCochainHom k D (p + 1) (s + 1) (n + 1) (by omega) w (T.d (n + 1) n ≫ φ) -
        slantCochainHom k D p (s + 1) n (by omega) (K.d (p + 1) p w) φ :=
  (sub_eq_of_eq_add' (slantCochain_d_comp_succ D p s n h w φ)).symm

private lemma slantCochainHom_d_zero (p : ℕ) (w : K.X (p + 1)) (φ : (T.linearYonedaObj k P).X p) :
    slantCochainHom k D p 0 p (add_zero p) (K.d (p + 1) p w) φ =
      slantCochainHom k D (p + 1) 0 (p + 1) (add_zero _) w (T.d (p + 1) p ≫ φ) :=
  slantCochain_d_zero D p w φ

/-- A cocycle slanted by a cycle is a cocycle. -/
private lemma d_comp_slantCochain_iCycles (p q n : ℕ) (h : p + q = n) (z : K.cycles p)
    (φ : T.X n ⟶ P) (hφ : T.d (n + 1) n ≫ φ = 0) :
    L.d (q + 1) q ≫ slantCochain k D p q n h (K.iCycles p z) φ = 0 := by
  obtain _ | r := p
  · obtain rfl : n = q := by omega
    rw [d_comp_slantCochain_zero, hφ, map_zero]
  · have hz : K.d (r + 1) r (K.iCycles (r + 1) z) = 0 :=
      (ConcreteCategory.comp_apply _ _ z).symm.trans
        (ConcreteCategory.congr_hom (K.iCycles_d _ _) z)
    have hd := slantCochain_d_comp_succ D r q n h (K.iCycles (r + 1) z) φ
    rw [hφ, map_zero, hz, map_zero, LinearMap.zero_apply, zero_add] at hd
    -- `(-1)^(r+1)` is its own inverse
    calc L.d (q + 1) q ≫ slantCochain k D (r + 1) q n h (K.iCycles (r + 1) z) φ
        = (((-1 : ℤ) ^ (r + 1)) * (-1) ^ (r + 1)) •
            (L.d (q + 1) q ≫ slantCochain k D (r + 1) q n h (K.iCycles (r + 1) z) φ) := by
          rw [← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]
      _ = 0 := by rw [mul_smul, ← hd, smul_zero]

/-- A cocycle slanted by a boundary: `φ / ∂w = (-1)^p δ(φ / w)` when `δφ = 0`. -/
private lemma slantCochain_d_of_d_comp_eq_zero (p s n : ℕ) (h : p + 1 + s = n)
    (w : K.X (p + 1)) (φ : T.X n ⟶ P) (hφ : T.d (n + 1) n ≫ φ = 0) :
    slantCochain k D p (s + 1) n (by omega) (K.d (p + 1) p w) φ =
      ((-1 : ℤ) ^ p) • (L.d (s + 1) s ≫ slantCochain k D (p + 1) s n h w φ) := by
  have hd := slantCochain_d_comp_succ D p s n h w φ
  rw [hφ, map_zero, eq_comm, add_eq_zero_iff_eq_neg, pow_succ, mul_neg_one, neg_smul,
    neg_neg] at hd
  exact hd

private lemma slantCochainHom_d_of_d_comp_eq_zero (p s n : ℕ) (h : p + 1 + s = n)
    (w : K.X (p + 1)) (φ : (T.linearYonedaObj k P).cycles n) :
    slantCochainHom k D p (s + 1) n (by omega) (K.d (p + 1) p w)
        ((T.linearYonedaObj k P).iCycles n φ) =
      ((-1 : ℤ) ^ p) • (L.d (s + 1) s ≫
        slantCochainHom k D (p + 1) s n h w ((T.linearYonedaObj k P).iCycles n φ)) :=
  slantCochain_d_of_d_comp_eq_zero D p s n h w _ (d_comp_linearYonedaObj_iCycles _ _ φ)

variable (k) in
/-- Slanting by a fixed cycle, as a map of cocycles. -/
private def slantCyclesLeft (p q n : ℕ) (h : p + q = n) (z : K.cycles p) :
    (T.linearYonedaObj k P).cycles n ⟶ (L.linearYonedaObj k P).cycles q :=
  (L.linearYonedaObj k P).liftCycles
    (ModuleCat.ofHom (slantCochainHom k D p q n h (K.iCycles p z) ∘ₗ
      ((T.linearYonedaObj k P).iCycles n).hom)) (q + 1) (by simp) (by
        ext φ
        exact d_comp_slantCochain_iCycles D p q n h z _ (d_comp_linearYonedaObj_iCycles _ _ φ))

private lemma iCycles_slantCyclesLeft (p q n : ℕ) (h : p + q = n) (z : K.cycles p)
    (φ : (T.linearYonedaObj k P).cycles n) :
    (L.linearYonedaObj k P).iCycles q (slantCyclesLeft k D p q n h z φ) =
      slantCochainHom k D p q n h (K.iCycles p z) ((T.linearYonedaObj k P).iCycles n φ) :=
  ConcreteCategory.congr_hom ((L.linearYonedaObj k P).liftCycles_i _ _ _ _) φ

variable (k) in
/-- **The slant product of a cycle and a cocycle**: the slant product
`TauCeti.ChainComplex.slantCochain` of the underlying chain and cochain, which is a cocycle by the
boundary formulas (`TauCeti.ChainComplex.iCycles_slantCycles`). -/
def slantCycles (p q n : ℕ) (h : p + q = n) :
    K.cycles p →ₗ[k] (T.linearYonedaObj k P).cycles n →ₗ[k] (L.linearYonedaObj k P).cycles q where
  toFun z := (slantCyclesLeft k D p q n h z).hom
  map_add' z z' := by
    ext φ
    apply HomologicalComplex.moduleCat_iCycles_injective
    simp [iCycles_slantCyclesLeft]
  map_smul' r z := by
    ext φ
    apply HomologicalComplex.moduleCat_iCycles_injective
    simp [iCycles_slantCyclesLeft]

/-- On underlying chains and cochains, the slant product of a cycle and a cocycle is the slant
product of the chain and the cochain. -/
@[simp]
lemma iCycles_slantCycles (p q n : ℕ) (h : p + q = n) (z : K.cycles p)
    (φ : (T.linearYonedaObj k P).cycles n) :
    (L.linearYonedaObj k P).iCycles q (slantCycles k D p q n h z φ) =
      slantCochain k D p q n h (K.iCycles p z) ((T.linearYonedaObj k P).iCycles n φ) :=
  iCycles_slantCyclesLeft D p q n h z φ

private lemma iCycles_slantCycles_slantCochainHom (p q n : ℕ) (h : p + q = n) (z : K.cycles p)
    (φ : (T.linearYonedaObj k P).cycles n) :
    (L.linearYonedaObj k P).iCycles q (slantCycles k D p q n h z φ) =
      slantCochainHom k D p q n h (K.iCycles p z) ((T.linearYonedaObj k P).iCycles n φ) :=
  iCycles_slantCyclesLeft D p q n h z φ

/-- A coboundary slanted by a cycle is a coboundary. -/
private lemma homologyπ_slantCycles_toCycles_right (p q n : ℕ) (h : p + q = n) (z : K.cycles p)
    (i : ℕ) (ψ : (T.linearYonedaObj k P).X i) :
    (L.linearYonedaObj k P).homologyπ q
      (slantCycles k D p q n h z ((T.linearYonedaObj k P).toCycles i n ψ)) = 0 := by
  by_cases hin : (ComplexShape.up ℕ).Rel i n
  · obtain rfl : i + 1 = n := hin
    obtain _ | r := p
    · obtain rfl : q = i + 1 := by omega
      -- by the boundary formula, `δψ / z = δ (ψ / z)`
      have key : slantCycles k D 0 (i + 1) (i + 1) h z
          ((T.linearYonedaObj k P).toCycles i (i + 1) ψ) =
          (L.linearYonedaObj k P).toCycles i (i + 1)
            (slantCochainHom k D 0 i i (zero_add i) (K.iCycles 0 z) ψ) := by
        apply HomologicalComplex.moduleCat_iCycles_injective
        rw [iCycles_slantCycles_slantCochainHom, linearYonedaObj_iCycles_toCycles_apply,
          linearYonedaObj_iCycles_toCycles_apply, d_comp_slantCochainHom_zero]
      rw [key, linearYonedaObj_homologyπ_toCycles_apply]
    · have hz : K.d (r + 1) r (K.iCycles (r + 1) z) = 0 :=
        (ConcreteCategory.comp_apply _ _ z).symm.trans
          (ConcreteCategory.congr_hom (K.iCycles_d _ _) z)
      obtain _ | s := q
      · -- in degree zero of `L`, `δψ / z = ψ / ∂z = 0`
        obtain rfl : r = i := by omega
        have key : slantCycles k D (r + 1) 0 (r + 1) h z
            ((T.linearYonedaObj k P).toCycles r (r + 1) ψ) = 0 := by
          apply HomologicalComplex.moduleCat_iCycles_injective
          rw [iCycles_slantCycles_slantCochainHom, linearYonedaObj_iCycles_toCycles_apply,
            ← slantCochainHom_d_zero, hz, map_zero, LinearMap.zero_apply, map_zero]
        rw [key, map_zero]
      -- by the boundary formula, `δψ / z = (-1)^(r+1) δ (ψ / z)`, since `∂z = 0`
      have key : slantCycles k D (r + 1) (s + 1) (i + 1) h z
          ((T.linearYonedaObj k P).toCycles i (i + 1) ψ) =
          ((-1 : ℤ) ^ (r + 1)) • (L.linearYonedaObj k P).toCycles s (s + 1)
            (slantCochainHom k D (r + 1) s i (by omega) (K.iCycles (r + 1) z) ψ) := by
        have hd := slantCochainHom_d_comp_succ (k := k) D r s i (by omega)
          (K.iCycles (r + 1) z) ψ
        rw [hz, map_zero, LinearMap.zero_apply, sub_zero] at hd
        apply HomologicalComplex.moduleCat_iCycles_injective
        rw [iCycles_slantCycles_slantCochainHom, map_zsmul, linearYonedaObj_iCycles_toCycles_apply,
          linearYonedaObj_iCycles_toCycles_apply, ← hd]
        rfl
      rw [key, map_zsmul, linearYonedaObj_homologyπ_toCycles_apply, smul_zero]
  · rw [(T.linearYonedaObj k P).toCycles_eq_zero hin]
    simp

/-- A cocycle slanted by a boundary is a coboundary. -/
private lemma homologyπ_slantCycles_toCycles_left (p q n : ℕ) (h : p + q = n) (i : ℕ)
    (w : K.X i) (φ : (T.linearYonedaObj k P).cycles n) :
    (L.linearYonedaObj k P).homologyπ q (slantCycles k D p q n h (K.toCycles i p w) φ) = 0 := by
  by_cases hip : (ComplexShape.down ℕ).Rel i p
  · obtain rfl : p + 1 = i := hip
    have hφ := d_comp_linearYonedaObj_iCycles (k := k) (X := T) (Y := P) n (n + 1) φ
    have hw : K.iCycles p (K.toCycles (p + 1) p w) = K.d (p + 1) p w :=
      ConcreteCategory.congr_hom (K.toCycles_i (p + 1) p) w
    obtain _ | s := q
    · -- in degree zero of `L`, `φ / ∂w = δφ / w = 0`
      obtain rfl : p = n := by omega
      have key : slantCycles k D p 0 p h (K.toCycles (p + 1) p w) φ = 0 := by
        apply HomologicalComplex.moduleCat_iCycles_injective
        rw [iCycles_slantCycles_slantCochainHom, hw, slantCochainHom_d_zero, hφ, map_zero,
          map_zero]
      rw [key, map_zero]
    · -- by the boundary formula, `φ / ∂w = (-1)^p δ (φ / w)`, since `δφ = 0`
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨p + s, by omega⟩
      have key : slantCycles k D p (s + 1) (m + 1) h (K.toCycles (p + 1) p w) φ =
          ((-1 : ℤ) ^ p) • (L.linearYonedaObj k P).toCycles s (s + 1)
            (slantCochainHom k D (p + 1) s (m + 1) (by omega) w
              ((T.linearYonedaObj k P).iCycles (m + 1) φ)) := by
        apply HomologicalComplex.moduleCat_iCycles_injective
        rw [iCycles_slantCycles_slantCochainHom, map_zsmul, linearYonedaObj_iCycles_toCycles_apply,
          hw, slantCochainHom_d_of_d_comp_eq_zero D p s (m + 1) (by omega)]
        rfl
      rw [key, map_zsmul, linearYonedaObj_homologyπ_toCycles_apply, smul_zero]
  · rw [K.toCycles_eq_zero hip]
    simp

variable (k) in
/-- Slanting by a fixed cycle, on cohomology. -/
private def slantHomologyLeft (p q n : ℕ) (h : p + q = n) (z : K.cycles p) :
    (T.linearYonedaObj k P).homology n ⟶ (L.linearYonedaObj k P).homology q :=
  (CokernelCofork.IsColimit.desc' ((T.linearYonedaObj k P).homologyIsCokernel _ n rfl)
    (ModuleCat.ofHom (slantCycles k D p q n h z) ≫ (L.linearYonedaObj k P).homologyπ q)
    (by
      ext ψ
      exact homologyπ_slantCycles_toCycles_right D p q n h z _ ψ)).1

private lemma slantHomologyLeft_homologyπ (p q n : ℕ) (h : p + q = n) (z : K.cycles p)
    (φ : (T.linearYonedaObj k P).cycles n) :
    (slantHomologyLeft k D p q n h z).hom ((T.linearYonedaObj k P).homologyπ n φ) =
      (L.linearYonedaObj k P).homologyπ q (slantCycles k D p q n h z φ) := by
  unfold slantHomologyLeft
  exact ConcreteCategory.congr_hom (CokernelCofork.IsColimit.desc'
    ((T.linearYonedaObj k P).homologyIsCokernel _ n rfl)
    (ModuleCat.ofHom (slantCycles k D p q n h z) ≫ (L.linearYonedaObj k P).homologyπ q) _).2 φ

variable (k) in
/-- Slanting by a cycle on cohomology, as a linear function of the cycle. -/
private def slantCyclesHomology (p q n : ℕ) (h : p + q = n) :
    K.cycles p ⟶
      ModuleCat.of k
        ((T.linearYonedaObj k P).homology n →ₗ[k] (L.linearYonedaObj k P).homology q) :=
  ModuleCat.ofHom (X := K.cycles p)
    { toFun z := (slantHomologyLeft k D p q n h z).hom
      map_add' z z' := LinearMap.ext fun α ↦ by
        obtain ⟨φ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ n α
        simp only [slantHomologyLeft_homologyπ, map_add, LinearMap.add_apply]
      map_smul' r z := LinearMap.ext fun α ↦ by
        obtain ⟨φ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ n α
        simp only [slantHomologyLeft_homologyπ, LinearMap.smul_apply, RingHom.id_apply]
        rw [map_smul, LinearMap.smul_apply, map_smul] }

private lemma toCycles_comp_slantCyclesHomology (p q n : ℕ) (h : p + q = n) :
    K.toCycles ((ComplexShape.down ℕ).prev p) p ≫ slantCyclesHomology k D (P := P) p q n h = 0 := by
  ext w : 2
  refine LinearMap.ext fun α ↦ ?_
  obtain ⟨φ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ n α
  exact (slantHomologyLeft_homologyπ D p q n h _ φ).trans
    (homologyπ_slantCycles_toCycles_left D p q n h _ w φ)

variable (k) in
/-- **The slant product on homology and cohomology**, `Hₚ(K) × Hⁿ(Hom(T, P)) ⟶ H^q(Hom(L, P))`
for `p + q = n`, along the chain map `D : K ⊗ L ⟶ T`: the class of `φ / z` on the classes of a
cycle `z` and a cocycle `φ` (`TauCeti.ChainComplex.slant_homologyπ`). -/
def slant (p q n : ℕ) (h : p + q = n) :
    K.homology p →ₗ[k] (T.linearYonedaObj k P).homology n →ₗ[k]
      (L.linearYonedaObj k P).homology q :=
  (CokernelCofork.IsColimit.desc' (K.homologyIsCokernel _ p rfl)
    (slantCyclesHomology k D p q n h) (toCycles_comp_slantCyclesHomology D p q n h)).1.hom

/-- **The slant product on classes**: the slant product of the classes of a cycle and a cocycle
is the class of their slant product. -/
@[simp]
lemma slant_homologyπ (p q n : ℕ) (h : p + q = n) (z : K.cycles p)
    (φ : (T.linearYonedaObj k P).cycles n) :
    slant k D p q n h (K.homologyπ p z) ((T.linearYonedaObj k P).homologyπ n φ) =
      (L.linearYonedaObj k P).homologyπ q (slantCycles k D p q n h z φ) := by
  have hfac := ConcreteCategory.congr_hom (CokernelCofork.IsColimit.desc'
    (K.homologyIsCokernel _ p rfl) (slantCyclesHomology k D (P := P) p q n h)
    (toCycles_comp_slantCyclesHomology D p q n h)).2 z
  rw [slant, ← slantHomologyLeft_homologyπ]
  exact LinearMap.congr_fun hfac _

/-- **The evaluation law of the slant product**, `⟨φ / x, y⟩ = ⟨φ, D_*(x × y)⟩`: the Kronecker
pairing of the slant product `φ / x` with a class `y ∈ H_q(L)` is the Kronecker pairing of `φ`
with the image under `D` of the homology cross product `x × y ∈ Hₙ(K ⊗ L)`. -/
theorem kronecker_slant (p q n : ℕ) (h : p + q = n) (x : K.homology p)
    (φ : (T.linearYonedaObj k P).homology n) (y : L.homology q) :
    kronecker k L P q (slant k D p q n h x φ) y =
      kronecker k T P n φ (homologyMap D n (homologyCross K L p q n h (x ⊗ₜ y))) := by
  obtain ⟨z, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p x
  obtain ⟨ψ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ n φ
  obtain ⟨w, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ q y
  have hcross := ConcreteCategory.congr_hom (homologyπ_tensorHom_homologyCross K L p q n h)
    (z ⊗ₜ w)
  have hi := ConcreteCategory.congr_hom (cyclesCross_iCycles K L p q n h) (z ⊗ₜ w)
  have hD := ConcreteCategory.congr_hom (homologyπ_naturality D n)
    (cyclesCross K L p q n h (z ⊗ₜ w))
  have hDi := ConcreteCategory.congr_hom (cyclesMap_i D n) (cyclesCross K L p q n h (z ⊗ₜ w))
  simp only [ConcreteCategory.comp_apply, ModuleCat.MonoidalCategory.tensorHom_tmul] at hcross hi
  simp only [ConcreteCategory.comp_apply] at hD hDi
  rw [slant_homologyπ, kronecker_homologyπ_homologyπ, hcross, hD, kronecker_homologyπ_homologyπ,
    iCycles_slantCycles, hDi, hi]
  exact slantCochain_apply D p q n h _ _ _

end Cohomology

/-- **Naturality of the slant product**: if chain maps `f : K' ⟶ K`, `g : L' ⟶ L` and
`e : T' ⟶ T` satisfy `(f ⊗ g) ≫ D = D' ≫ e`, then `e^* φ / x = g^* (φ / f_* x)` for classes
`x ∈ Hₚ(K')` and `φ ∈ Hⁿ(Hom(T, P))`. -/
lemma slant_naturality {K' L' T' : ChainComplex (ModuleCat.{u} k) ℕ} [K'.HasTensor L']
    (D' : HomologicalComplex.tensorObj K' L' ⟶ T') (f : K' ⟶ K) (g : L' ⟶ L) (e : T' ⟶ T)
    (hD : HomologicalComplex.tensorHom f g ≫ D = D' ≫ e) (p q n : ℕ) (h : p + q = n)
    (x : K'.homology p) (φ : (T.linearYonedaObj k P).homology n) :
    slant k D' p q n h x
        (homologyMap (K := T.linearYonedaObj k P) (L := T'.linearYonedaObj k P)
          ((linearYonedaFunctor k P).map e.op) n φ) =
      homologyMap (K := L.linearYonedaObj k P) (L := L'.linearYonedaObj k P)
        ((linearYonedaFunctor k P).map g.op) q (slant k D p q n h (homologyMap f p x) φ) := by
  obtain ⟨z, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p x
  obtain ⟨ψ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ n φ
  have hf := ConcreteCategory.congr_hom (homologyπ_naturality f p) z
  have hfi := ConcreteCategory.congr_hom (cyclesMap_i f p) z
  simp only [ConcreteCategory.comp_apply] at hf hfi
  rw [homologyMap_linearYonedaFunctor_map_homologyπ_apply, slant_homologyπ, hf, slant_homologyπ,
    homologyMap_linearYonedaFunctor_map_homologyπ_apply]
  congr 1
  apply HomologicalComplex.moduleCat_iCycles_injective
  rw [iCycles_slantCycles, iCycles_cyclesMap_linearYonedaFunctor_map_apply,
    iCycles_cyclesMap_linearYonedaFunctor_map_apply, iCycles_slantCycles, hfi]
  exact slantCochain_naturality D D' f g e hD p q n h _ _

end TauCeti.ChainComplex
