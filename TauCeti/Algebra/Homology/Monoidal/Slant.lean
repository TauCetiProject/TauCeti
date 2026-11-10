/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import TauCeti.Algebra.Category.ModuleCat.Monoidal.TensorMk
public import TauCeti.Algebra.Homology.Bifunctor.Homotopy
public import TauCeti.Algebra.Homology.HomologicalComplex.ZeroDifferential
public import TauCeti.Algebra.Homology.Kronecker
public import TauCeti.Algebra.Homology.Monoidal.Cup
public import TauCeti.Algebra.Homology.Monoidal.Homology.Cross
public import TauCeti.Algebra.Homology.Monoidal.Tensor.Differential
public import TauCeti.Algebra.Homology.Split

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

Slanting by a cycle `z` of degree zero is a pullback: if `v ↦ e (D (z ⊗ v))` is a chain map
`c : L ⟶ T'` for some chain map `e : T ⟶ T'`, then `e^* φ / [z] = c^* φ`
(`TauCeti.ChainComplex.slant_homologyπ_zero_homologyMap`).

The slant product of singular cohomology, `Hⁿ(X × Y) × Hₚ(X) ⟶ H^q(Y)`, is the case where `D` is
the shuffle map; it produces, for instance, the classes `c₁(U) / γ ∈ H¹(Y)` of a line bundle `U`
on `X × Y` and loops `γ` in `X`.

For `D` the identity of `K ⊗ L`, the slant product computes cup products of cochains on the two
factors: `(a ⌣ b) / x` is `b` with its coefficients changed along `n ↦ μ (⟨a, x⟩ ⊗ n)`
(`TauCeti.ChainComplex.slant_cup`), and it vanishes when the degrees of `a` and `x` differ
(`TauCeti.ChainComplex.slant_cup_of_ne`). Conversely, when the terms and the homology of `K` are
projective, a class of `Hⁿ(Hom(K ⊗ L, P))` is determined by its slant products by the homology
classes of `K` (`TauCeti.ChainComplex.eq_zero_of_forall_slant_eq_zero`). Indeed `K` is then
homotopy equivalent to a complex `K'` of projectives with zero differentials
(`HomologicalComplex.exists_homotopyEquiv_d_eq_zero`). A cocycle `c` of `Hom(K' ⊗ L, P)` is a
family of maps `K'_p ⟶ Hom(L_q, P)` into the cocycles of `L`; when its slant classes vanish these
maps land in the coboundaries, and lift, `K'_p` being projective, to maps into `Hom(L_{q-1}, P)`
which assemble into a cochain with coboundary `c`. With no hypothesis on `L`, these two facts are
the algebraic content of the Künneth theorem for the cohomology of a product one of whose factors
has finitely generated projective homology.

## Main definitions and results

* `TauCeti.ChainComplex.slantCochain`: the slant product of a chain and a cochain.
* `TauCeti.ChainComplex.d_comp_slantCochain_zero`, `TauCeti.ChainComplex.slantCochain_d_comp_succ`
  and `TauCeti.ChainComplex.slantCochain_d_zero`: the boundary formulas.
* `TauCeti.ChainComplex.slantCycles`: the slant product of a cycle and a cocycle.
* `TauCeti.ChainComplex.slant`: the slant product on homology and cohomology, with
  `TauCeti.ChainComplex.slant_homologyπ` computing it on classes of cycles and cocycles.
* `TauCeti.ChainComplex.kronecker_slant`: the evaluation law `⟨φ / x, y⟩ = ⟨φ, D_*(x × y)⟩`.
* `TauCeti.ChainComplex.slant_naturality`: naturality.
* `TauCeti.ChainComplex.slant_homologyπ_zero_homologyMap`: the slant product by a cycle of degree
  zero along which `D` restricts to a chain map.
* `TauCeti.ChainComplex.slantCochain_cupCochain`, `TauCeti.ChainComplex.slant_cup` and
  `TauCeti.ChainComplex.slant_cup_of_ne`: slant products of cup products along the identity of
  `K ⊗ L`.
* `TauCeti.ChainComplex.eq_zero_of_forall_slant_eq_zero`: slant products by homology classes of a
  complex with projective terms and homology detect the cohomology of `Hom(K ⊗ L, P)`.

## References

* E. H. Spanier, *Algebraic Topology*, McGraw–Hill, 1966, Chapter 6 (the slant product).
* A. Dold, *Lectures on Algebraic Topology*, Springer, 1972, Chapter VII (products).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Theorem 3.15 and Section 3.B, the Künneth formulas.
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
  simp only [slantCochain_eq, ConcreteCategory.comp_apply, ModuleCat.tensorMk_apply]

/-- **The boundary formula for the slant product by a chain of degree zero**: the coboundary of
`φ / z` is `δφ / z`. -/
lemma d_comp_slantCochain_zero (q : ℕ) (z : K.X 0) (φ : T.X q ⟶ P) :
    L.d (q + 1) q ≫ slantCochain k D 0 q q (zero_add q) z φ =
      slantCochain k D 0 (q + 1) (q + 1) (zero_add _) z (T.d (q + 1) q ≫ φ) := by
  rw [slantCochain_eq, slantCochain_eq, D.comm_assoc, mapBifunctor.d_eq,
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
  rw [slantCochain_eq, slantCochain_eq, slantCochain_eq, D.comm_assoc, mapBifunctor.d_eq]
  simp only [Preadditive.add_comp, Preadditive.comp_add,
    ChainComplex.ιTensorObj_D₁_succ_assoc, ChainComplex.ιTensorObj_D₂_succ_assoc,
    Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc,
    ModuleCat.tensorMk_whiskerRight_assoc, ModuleCat.comp_tensorMk_assoc]

/-- **The slant product by a boundary, in degree zero of `L`**: for a chain `w ∈ K_{p+1}`,
`φ / ∂w = δφ / w` on `L_0`. -/
lemma slantCochain_d_zero (p : ℕ) (w : K.X (p + 1)) (φ : T.X p ⟶ P) :
    slantCochain k D p 0 p (add_zero p) (K.d (p + 1) p w) φ =
      slantCochain k D (p + 1) 0 (p + 1) (add_zero _) w (T.d (p + 1) p ≫ φ) := by
  rw [slantCochain_eq, slantCochain_eq, D.comm_assoc, mapBifunctor.d_eq]
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
  · have hz := K.iCycles_d_apply (r + 1) r z
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
    · have hz := K.iCycles_d_apply (r + 1) r z
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
        -- the two sides differ only in their `ℤ`-action: one is that of the hom group
        -- `L.X (s + 1) ⟶ P`, the other that of the cochain module
        -- `(L.linearYonedaObj k P).X (s + 1)`; these agree by unfolding `linearYonedaObj`
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
        -- the two sides differ only in their `ℤ`-action: one is that of the hom group
        -- `L.X (s + 1) ⟶ P`, the other that of the cochain module
        -- `(L.linearYonedaObj k P).X (s + 1)`; these agree by unfolding `linearYonedaObj`
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

/-- **The slant product by a cycle of degree zero**: let `z` be a cycle of degree zero, `e : T ⟶ T'`
a chain map and `c : L ⟶ T'` a chain map with `c (v) = e (D (z ⊗ v))` in degree `q`. Then
`e^* φ / [z] = c^* φ` for every class `φ ∈ H^q(Hom(T', P))`. For the shuffle map of singular chains,
`z` a point of `X` and `e` induced by the projection `X × Y ⟶ Y`, the composite
`v ↦ e (D (z ⊗ v))` is the identity, so slanting a class pulled back from `Y` by a point returns it
(`TopCat.singularSlant_homologyπ_singularCohomologyMap_snd`). -/
lemma slant_homologyπ_zero_homologyMap {T' : ChainComplex (ModuleCat.{u} k) ℕ} (e : T ⟶ T')
    (c : L ⟶ T') (z : K.cycles 0) (q : ℕ)
    (hc : ModuleCat.tensorMk (K.iCycles 0 z) ≫ ιTensorObj K L 0 q q (zero_add q) ≫ D.f q ≫
      e.f q = c.f q)
    (φ : (T'.linearYonedaObj k P).homology q) :
    slant k D 0 q q (zero_add q) (K.homologyπ 0 z)
        (homologyMap (K := T'.linearYonedaObj k P) (L := T.linearYonedaObj k P)
          ((linearYonedaFunctor k P).map e.op) q φ) =
      homologyMap (K := T'.linearYonedaObj k P) (L := L.linearYonedaObj k P)
        ((linearYonedaFunctor k P).map c.op) q φ := by
  obtain ⟨ψ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ q φ
  rw [homologyMap_linearYonedaFunctor_map_homologyπ_apply, slant_homologyπ,
    homologyMap_linearYonedaFunctor_map_homologyπ_apply]
  congr 1
  apply HomologicalComplex.moduleCat_iCycles_injective
  rw [iCycles_slantCycles, iCycles_cyclesMap_linearYonedaFunctor_map_apply,
    iCycles_cyclesMap_linearYonedaFunctor_map_apply, ← hc]
  exact ModuleCat.hom_ext (LinearMap.ext fun v ↦ rfl)

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

section CupProduct

variable {M N : ModuleCat.{u} k} (μ : M ⊗ N ⟶ P)

/-- **The slant product of a cup product of cochains**, along the identity of `K ⊗ L`: slanting
`φ ⌣ ψ` by `z ∈ K_p` gives `ψ` followed by the coefficient map `n ↦ μ (φ z ⊗ n)`. -/
lemma slantCochain_cupCochain (p q n : ℕ) (h : p + q = n) (z : K.X p) (φ : K.X p ⟶ M)
    (ψ : L.X q ⟶ N) :
    slantCochain k (𝟙 (HomologicalComplex.tensorObj K L)) p q n h z
        (cupCochain k (𝟙 (HomologicalComplex.tensorObj K L)) μ p q n h φ ψ) =
      ψ ≫ ModuleCat.tensorMk (φ z) ≫ μ := by
  ext v
  have hv := ConcreteCategory.congr_hom (ιTensorObj_tensorCochain μ φ ψ n h) (z ⊗ₜ v)
  simp only [ConcreteCategory.comp_apply, ModuleCat.MonoidalCategory.tensorHom_tmul] at hv
  simp only [slantCochain_apply, cupCochain_apply, HomologicalComplex.id_f,
    ConcreteCategory.comp_apply, ConcreteCategory.id_apply, ModuleCat.tensorMk_apply, hv]

/-- The slant product of a cup product of cochains of degrees `p` and `q` by a chain of degree
`p' ≠ p` vanishes. -/
lemma slantCochain_cupCochain_of_ne {p q p' q' n : ℕ} (h : p + q = n) (h' : p' + q' = n)
    (hp : p' ≠ p) (z : K.X p') (φ : K.X p ⟶ M) (ψ : L.X q ⟶ N) :
    slantCochain k (𝟙 (HomologicalComplex.tensorObj K L)) p' q' n h' z
        (cupCochain k (𝟙 (HomologicalComplex.tensorObj K L)) μ p q n h φ ψ) = 0 := by
  ext v
  simp only [slantCochain_apply, cupCochain_apply, HomologicalComplex.id_f, Category.id_comp]
  exact ConcreteCategory.congr_hom (ιTensorObj_tensorCochain_of_ne_left μ φ ψ h' hp) (z ⊗ₜ v)

/-- **The slant product of a cup product of classes**, along the identity of `K ⊗ L`:
`(a ⌣ b) / x` is the class `b` with its coefficients changed along `n ↦ μ (⟨a, x⟩ ⊗ n)`. For
coefficients in the ring itself and `μ` the multiplication, this is `⟨a, x⟩ • b`. -/
@[simp]
theorem slant_cup (p q n : ℕ) (h : p + q = n) (x : K.homology p)
    (a : (K.linearYonedaObj k M).homology p) (b : (L.linearYonedaObj k N).homology q) :
    slant k (𝟙 (HomologicalComplex.tensorObj K L)) p q n h x
        (cup k (𝟙 (HomologicalComplex.tensorObj K L)) μ p q n h a b) =
      homologyMap (L.linearYonedaObjMap k (ModuleCat.tensorMk (kronecker k K M p a x) ≫ μ)) q
        b := by
  obtain ⟨z, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p x
  obtain ⟨α, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p a
  obtain ⟨β, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ q b
  rw [cup_homologyπ, slant_homologyπ, L.homologyMap_linearYonedaObjMap_homologyπ_apply k,
    kronecker_homologyπ_homologyπ]
  congr 1
  apply HomologicalComplex.moduleCat_iCycles_injective
  rw [iCycles_slantCycles, iCycles_cupCycles, L.iCycles_cyclesMap_linearYonedaObjMap_apply k]
  exact slantCochain_cupCochain μ p q n h _ _ _

/-- The slant product of a cup product of classes of degrees `p` and `q` by a homology class of
degree `p' ≠ p` vanishes. -/
@[simp]
theorem slant_cup_of_ne {p q p' q' n : ℕ} (h : p + q = n) (h' : p' + q' = n) (hp : p' ≠ p)
    (x : K.homology p') (a : (K.linearYonedaObj k M).homology p)
    (b : (L.linearYonedaObj k N).homology q) :
    slant k (𝟙 (HomologicalComplex.tensorObj K L)) p' q' n h' x
        (cup k (𝟙 (HomologicalComplex.tensorObj K L)) μ p q n h a b) = 0 := by
  obtain ⟨z, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p' x
  obtain ⟨α, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p a
  obtain ⟨β, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ q b
  have hz : slantCycles k (𝟙 (HomologicalComplex.tensorObj K L)) p' q' n h' z
      (cupCycles k (𝟙 (HomologicalComplex.tensorObj K L)) μ p q n h α β) = 0 := by
    apply HomologicalComplex.moduleCat_iCycles_injective
    rw [iCycles_slantCycles, iCycles_cupCycles, map_zero]
    exact slantCochain_cupCochain_of_ne μ h h' hp _ _ _
  rw [cup_homologyπ, slant_homologyπ, hz, map_zero]

end CupProduct

section Detection

/-- If `K` has zero differentials and `K_p` is projective, and the slant products of a cocycle `c`
of `Hom(K ⊗ L, P)` by the elements of `K_p` are coboundaries in degree `s + 1`, then they are the
coboundaries of cochains `E z` of degree `s` depending linearly on `z ∈ K_p`. -/
private lemma exists_d_comp_eq_slantCochain (hK : ∀ i j, K.d i j = 0) {p s n : ℕ}
    [Projective (K.X p)] (h : p + (s + 1) = n)
    (c : (ChainComplex.linearYonedaObj (HomologicalComplex.tensorObj K L) k P).cycles n)
    (hc : ∀ z : K.cycles p, (L.linearYonedaObj k P).homologyπ (s + 1)
      (slantCycles k (𝟙 _) p (s + 1) n h z c) = 0) :
    ∃ E : K.X p →ₗ[k] (L.linearYonedaObj k P).X s, ∀ z, L.d (s + 1) s ≫ E z =
      slantCochain k (𝟙 _) p (s + 1) n h z
        ((ChainComplex.linearYonedaObj (HomologicalComplex.tensorObj K L) k P).iCycles n c) := by
  have := K.isIso_iCycles p _ rfl (hK _ _)
  let G : K.X p →ₗ[k] (L.linearYonedaObj k P).cycles (s + 1) :=
    (slantCycles k (𝟙 _) p (s + 1) n h).flip c ∘ₗ (inv (K.iCycles p)).hom
  have hG (z : K.X p) :
      G z ∈ LinearMap.range ((L.linearYonedaObj k P).toCycles s (s + 1)).hom :=
    ((L.linearYonedaObj k P).moduleCat_homologyπ_eq_zero_iff (by simp) _).1 (hc _)
  -- lift `G` through the surjection of the cochains of degree `s` onto the coboundaries
  obtain ⟨E, hE⟩ := Module.projective_lifting_property
    ((L.linearYonedaObj k P).toCycles s (s + 1)).hom.rangeRestrict
    (G.codRestrict _ hG) (LinearMap.surjective_rangeRestrict _)
  refine ⟨E, fun z ↦ ?_⟩
  have hEz := congrArg Subtype.val (LinearMap.congr_fun hE z)
  simp only [LinearMap.comp_apply, LinearMap.rangeRestrict, LinearMap.codRestrict_apply] at hEz
  have hz : K.iCycles p (inv (K.iCycles p) z) = z := by
    rw [← ModuleCat.comp_apply, IsIso.inv_hom_id, ModuleCat.id_apply]
  rw [← linearYonedaObj_iCycles_toCycles_apply, hEz]
  simp [G, hz]

/-- If `K` has zero differentials, a cocycle `c` of `Hom(K ⊗ L, P)` of degree `m + 1` is a
coboundary as soon as it vanishes on `K_{m+1} ⊗ L_0` and its slant products by the elements
`z ∈ K_p` are the coboundaries `δ (E z)` of cochains `E z` depending linearly on `z`: on the
summand `K_i ⊗ L_j` of degree `m` the cochain is `(-1)^i E`. -/
private lemma exists_toCycles_eq (hK : ∀ i j, K.d i j = 0) {m : ℕ}
    (c : (ChainComplex.linearYonedaObj (HomologicalComplex.tensorObj K L) k P).cycles (m + 1))
    (hzero : ∀ (z : K.X (m + 1)) (v : L.X 0),
      ConcreteCategory.hom (X := (HomologicalComplex.tensorObj K L).X (m + 1)) (Y := P)
        ((ChainComplex.linearYonedaObj (HomologicalComplex.tensorObj K L) k P).iCycles (m + 1) c)
        (ιTensorObj K L (m + 1) 0 (m + 1) (add_zero _) (z ⊗ₜ v)) = 0)
    (E : ∀ p s, p + (s + 1) = m + 1 → K.X p →ₗ[k] (L.linearYonedaObj k P).X s)
    (hE : ∀ p s (h : p + (s + 1) = m + 1) z, L.d (s + 1) s ≫ E p s h z =
      slantCochain k (𝟙 _) p (s + 1) (m + 1) h z
        ((ChainComplex.linearYonedaObj (HomologicalComplex.tensorObj K L) k P).iCycles (m + 1)
          c)) :
    ∃ ψ, (ChainComplex.linearYonedaObj (HomologicalComplex.tensorObj K L) k P).toCycles
        m (m + 1) ψ = c := by
  let ψ : (ChainComplex.linearYonedaObj (HomologicalComplex.tensorObj K L) k P).X m :=
    mapBifunctorDesc fun i j (hij : i + j = m) ↦ ((-1 : ℤ) ^ i) • ModuleCat.ofHom
      (TensorProduct.lift (ModuleCat.homLinearEquiv.toLinearMap ∘ₗ E i j (by omega)))
  refine ⟨ψ, ?_⟩
  apply HomologicalComplex.moduleCat_iCycles_injective
  rw [linearYonedaObj_iCycles_toCycles_apply]
  refine mapBifunctor.hom_ext fun p q (h : p + q = m + 1) ↦ ?_
  rw [mapBifunctor.d_eq, Preadditive.add_comp, Preadditive.comp_add]
  -- the part of the differential coming from `K` vanishes
  have hD₁ : ιTensorObj K L p q (m + 1) h ≫
      mapBifunctor.D₁ K L (curriedTensor _) (ComplexShape.down ℕ) (m + 1) m = 0 := by
    obtain _ | r := p
    · obtain rfl : q = m + 1 := by omega
      exact ChainComplex.ιTensorObj_D₁_zero K L m
    · rw [ChainComplex.ιTensorObj_D₁_succ K L r q m h, hK, MonoidalPreadditive.zero_whiskerRight,
        zero_comp]
  rw [reassoc_of% hD₁, zero_comp, zero_add]
  obtain _ | s := q
  · obtain rfl : p = m + 1 := by omega
    rw [reassoc_of% ChainComplex.ιTensorObj_D₂_zero K L m, zero_comp]
    exact ModuleCat.MonoidalCategory.tensor_ext fun z v ↦ (hzero z v).symm
  · rw [ChainComplex.ιTensorObj_D₂_succ_assoc K L p s m h, Preadditive.zsmul_comp,
      Category.assoc, ιTensorObj, ι_mapBifunctorDesc]
    refine ModuleCat.MonoidalCategory.tensor_ext fun z v ↦ ?_
    have hEz := congrArg (fun f ↦ ConcreteCategory.hom (X := L.X (s + 1)) (Y := P) f v)
      (hE p s h z)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zsmul,
      LinearMap.smul_apply, ModuleCat.MonoidalCategory.whiskerLeft_apply,
      ModuleCat.hom_ofHom, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]
    exact hEz.trans (slantCochain_apply _ _ _ _ _ _ _ _)

/-- Slant products by the elements of `K` detect the cohomology of `Hom(K ⊗ L, P)` when `K` is a
complex of projectives with zero differentials. -/
private theorem eq_zero_of_forall_slant_eq_zero_of_d_eq_zero (hK : ∀ i j, K.d i j = 0)
    [∀ p, Projective (K.X p)] {n : ℕ}
    (φ : (ChainComplex.linearYonedaObj (HomologicalComplex.tensorObj K L) k P).homology n)
    (hφ : ∀ p q (h : p + q = n) (x : K.homology p),
      slant k (𝟙 (HomologicalComplex.tensorObj K L)) p q n h x φ = 0) : φ = 0 := by
  obtain ⟨c, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ n φ
  have hcob (p q : ℕ) (h : p + q = n) (z : K.cycles p) :
      (L.linearYonedaObj k P).homologyπ q (slantCycles k (𝟙 _) p q n h z c) = 0 := by
    rw [← slant_homologyπ]
    exact hφ p q h _
  -- in degree zero of `L` the slant products of `c` vanish
  have hzero (z : K.X n) (v : L.X 0) :
      ConcreteCategory.hom (X := (HomologicalComplex.tensorObj K L).X n) (Y := P)
        ((ChainComplex.linearYonedaObj (HomologicalComplex.tensorObj K L) k P).iCycles n c)
        (ιTensorObj K L n 0 n (add_zero n) (z ⊗ₜ v)) = 0 := by
    have := K.isIso_iCycles n _ rfl (hK _ _)
    have hv := congrArg (fun a ↦ ConcreteCategory.hom (X := L.X 0) (Y := P)
      ((L.linearYonedaObj k P).iCycles 0 a) v)
      ((L.linearYonedaObj k P).moduleCat_eq_zero_of_homologyπ_eq_zero (by simp) _
        (hcob n 0 (add_zero n) (inv (K.iCycles n) z)))
    have hz : K.iCycles n (inv (K.iCycles n) z) = z := by
      rw [← ModuleCat.comp_apply, IsIso.inv_hom_id, ModuleCat.id_apply]
    simp only [iCycles_slantCycles, hz, map_zero] at hv
    exact (slantCochain_apply _ _ _ _ _ _ _ _).symm.trans hv
  cases n with
  | zero =>
    have hc : c = 0 := by
      apply HomologicalComplex.moduleCat_iCycles_injective
      rw [map_zero]
      refine mapBifunctor.hom_ext fun p q (h : p + q = 0) ↦ ?_
      obtain ⟨rfl, rfl⟩ : p = 0 ∧ q = 0 := by omega
      exact ModuleCat.MonoidalCategory.tensor_ext fun z v ↦ hzero z v
    rw [hc, map_zero]
  | succ m =>
    -- in positive degrees of `L` the slant products of `c` are coboundaries, linearly in `z`
    choose E hE using fun p s h ↦ exists_d_comp_eq_slantCochain hK h c (hcob p (s + 1) h)
    obtain ⟨ψ, rfl⟩ := exists_toCycles_eq hK c hzero E hE
    rw [linearYonedaObj_homologyπ_toCycles_apply]

/-- **Slant products detect the cohomology of a tensor product**: if the terms and the homology
objects of `K` are projective, a class `φ` of `Hⁿ(Hom(K ⊗ L, P))` whose slant products
`φ / x ∈ H^q(Hom(L, P))` by all homology classes `x ∈ Hₚ(K)`, `p + q = n`, vanish is zero. There
is no hypothesis on `L`. -/
theorem eq_zero_of_forall_slant_eq_zero [∀ p, Projective (K.X p)]
    [∀ p, Projective (K.homology p)] {n : ℕ}
    (φ : (ChainComplex.linearYonedaObj (HomologicalComplex.tensorObj K L) k P).homology n)
    (hφ : ∀ p q (h : p + q = n) (x : K.homology p),
      slant k (𝟙 (HomologicalComplex.tensorObj K L)) p q n h x φ = 0) : φ = 0 := by
  have := K.isSplitMono_iCycles_of_projective_homology
  -- `K` is homotopy equivalent to a complex `K'` of projectives with zero differentials
  obtain ⟨K', hK', ⟨e⟩⟩ := K.exists_homotopyEquiv_d_eq_zero
  have (p : ℕ) : Projective (K'.X p) :=
    Projective.of_iso (e.toHomologyIso p ≪≫
      (K'.XIsoHomologyOfDEqZero p (hK' _ _) (hK' _ _)).symm) inferInstance
  -- pulling back along `e.inv ⊗ 𝟙` is injective on cohomology and preserves vanishing slants
  let H := (HomotopyEquiv.mapBifunctor (curriedTensor _) (ComplexShape.down ℕ) e
    (HomotopyEquiv.refl L)).linearYonedaFunctorMap k P
  have hH :
      H.inv = (linearYonedaFunctor k P).map (HomologicalComplex.tensorHom e.inv (𝟙 L)).op := by
    simp only [H, HomotopyEquiv.linearYonedaFunctorMap_inv, HomotopyEquiv.mapBifunctor_inv,
      HomotopyEquiv.refl_inv]
  have : IsIso (homologyMap H.inv n) := (H.toHomologyIso n).isIso_inv
  rw [hH] at this
  refine (ModuleCat.mono_iff_injective (homologyMap
      ((linearYonedaFunctor k P).map (HomologicalComplex.tensorHom e.inv (𝟙 L)).op) n)).1
    inferInstance
    ((eq_zero_of_forall_slant_eq_zero_of_d_eq_zero hK' _ fun p q h x ↦ ?_).trans
      (map_zero _).symm)
  refine (slant_naturality (𝟙 (HomologicalComplex.tensorObj K L))
    (𝟙 (HomologicalComplex.tensorObj K' L)) e.inv (𝟙 L) (HomologicalComplex.tensorHom e.inv (𝟙 L))
    (by simp) p q n h x φ).trans ?_
  rw [hφ, map_zero]

end Detection

end TauCeti.ChainComplex
