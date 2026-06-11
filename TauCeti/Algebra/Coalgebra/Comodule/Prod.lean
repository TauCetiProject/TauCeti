/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Prod
import TauCeti.Algebra.Coalgebra.Comodule.Hom

/-!
# Products of comodules

For two right `C`-comodules `M` and `N` over an `R`-coalgebra `C`, this file equips the
product module `M × N` with the canonical right `C`-coaction
`(m, n) ↦ ι_M(ρ_M m) + ι_N(ρ_N n)`, where `ι_M`, `ι_N` are the inclusions into the first and
second summand. With this structure the projections `M × N → M`, `M × N → N` and the
inclusions `M → M × N`, `N → M × N` are comodule morphisms, and the universal properties of
the product and the coproduct hold, so `M × N` is simultaneously the product and the coproduct
of `M` and `N`: a direct sum of comodules.

This file stays at the unbundled `Comodule.Hom` level. The bundled `ComoduleCat`
product/coproduct/biproduct instances for the finite-dimensional representation category are a
separate categorical layer; the maps and uniqueness lemmas here are the prerequisite
unbundled product/coproduct API.

## Main definitions

* `TauCeti.Comodule.instProd`: the right `C`-comodule structure on `M × N`.
* `TauCeti.Comodule.Hom.fst`, `TauCeti.Comodule.Hom.snd`: the projection comodule morphisms.
* `TauCeti.Comodule.Hom.inl`, `TauCeti.Comodule.Hom.inr`: the inclusion comodule morphisms.
* `TauCeti.Comodule.Hom.prod`, `TauCeti.Comodule.Hom.coprod`: the morphisms induced by the
  universal properties of the product and the coproduct, characterized by
  `fst_comp_prod`/`snd_comp_prod` and `coprod_comp_inl`/`coprod_comp_inr` together with the
  uniqueness lemmas `prod_ext`/`coprod_ext`, with the biproduct relations `fst_comp_inl`,
  `snd_comp_inl`, `fst_comp_inr`, `snd_comp_inr`, and `coprod_inl_inr`.

## References

This is the standard direct sum of comodules; see for example Sweedler, *Hopf Algebras*,
Chapter 2. It supplies an unbundled product/coproduct prerequisite for
`TauCetiRoadmap/ReductiveGroups/README.md`, Layer 1, "Comodules over a coalgebra/Hopf
algebra". It reuses Mathlib's `TensorProduct.assoc` associativity coherence and the
`rTensor`/`lTensor` calculus from `Mathlib.LinearAlgebra.TensorProduct.Map`.
-/

open scoped TensorProduct

namespace TauCeti

universe u v w x y

namespace Comodule

variable {R : Type u} {C : Type v} {M : Type w} {N : Type x} {P : Type y}
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]
variable [AddCommMonoid N] [Module R N] [Comodule R C N]
variable [AddCommMonoid P] [Module R P] [Comodule R C P]

local notation "ρM" => coact (R := R) (C := C) (M := M)
local notation "ρN" => coact (R := R) (C := C) (M := N)

/-- The coaction of the product comodule `M × N`: coact on each factor, then include into the
corresponding summand. This is the implementation of the `Comodule R C (M × N)` instance; the
public characterizing equations are `prod_coact_apply`, `prod_coact_inl`, and `prod_coact_inr`. -/
private noncomputable def prodCoact : (M × N) →ₗ[R] (M × N) ⊗[R] C :=
  (LinearMap.inl R M N).rTensor C ∘ₗ ρM ∘ₗ LinearMap.fst R M N
    + (LinearMap.inr R M N).rTensor C ∘ₗ ρN ∘ₗ LinearMap.snd R M N

@[simp]
private theorem prodCoact_comp_inl :
    prodCoact ∘ₗ LinearMap.inl R M N = (LinearMap.inl R M N).rTensor C ∘ₗ ρM := by
  ext m; simp [prodCoact]

@[simp]
private theorem prodCoact_comp_inr :
    prodCoact ∘ₗ LinearMap.inr R M N = (LinearMap.inr R M N).rTensor C ∘ₗ ρN := by
  ext n; simp [prodCoact]

private theorem prodCoact_apply (m : M) (n : N) :
    prodCoact (m, n) = (LinearMap.inl R M N).rTensor C (ρM m)
      + (LinearMap.inr R M N).rTensor C (ρN n) := by
  simp [prodCoact]

/-- `prodCoact` on a first-summand inclusion is the included coaction. -/
private theorem prodCoact_inl_apply (m : M) :
    prodCoact (LinearMap.inl R M N m) = (LinearMap.inl R M N).rTensor C (ρM m) :=
  LinearMap.congr_fun prodCoact_comp_inl m

/-- `prodCoact` on a second-summand inclusion is the included coaction. -/
private theorem prodCoact_inr_apply (n : N) :
    prodCoact (LinearMap.inr R M N n) = (LinearMap.inr R M N).rTensor C (ρN n) :=
  LinearMap.congr_fun prodCoact_comp_inr n

private theorem prodCoassoc_inl (m : M) :
    TensorProduct.assoc R (M × N) C C (prodCoact.rTensor C (prodCoact (LinearMap.inl R M N m)))
      = Coalgebra.comul.lTensor (M × N) (prodCoact (LinearMap.inl R M N m)) := by
  rw [prodCoact_inl_apply]
  rw [← LinearMap.comp_apply (prodCoact.rTensor C), ← LinearMap.rTensor_comp,
    prodCoact_comp_inl, LinearMap.rTensor_comp]
  have h :
      TensorProduct.assoc R (M × N) C C
        ((LinearMap.rTensor C (LinearMap.rTensor C (LinearMap.inl R M N)) ∘ₗ
          LinearMap.rTensor C (coact (R := R) (C := C) (M := M))) (ρM m))
        = (LinearMap.inl R M N).rTensor (C ⊗[R] C)
          (TensorProduct.assoc R M C C
            ((coact (R := R) (C := C) (M := M)).rTensor C (ρM m))) := by
    simp only [LinearMap.comp_apply]
    simpa [LinearMap.rTensor] using
      (TensorProduct.map_map_assoc (LinearMap.inl R M N) LinearMap.id LinearMap.id
        ((coact (R := R) (C := C) (M := M)).rTensor C (ρM m))).symm
  rw [h, coassoc_apply]
  rw [← LinearMap.comp_apply (Coalgebra.comul.lTensor (M × N)),
    LinearMap.lTensor_comp_rTensor, ← LinearMap.comp_apply (LinearMap.rTensor (C ⊗[R] C) _),
    LinearMap.rTensor_comp_lTensor]

private theorem prodCoassoc_inr (n : N) :
    TensorProduct.assoc R (M × N) C C (prodCoact.rTensor C (prodCoact (LinearMap.inr R M N n)))
      = Coalgebra.comul.lTensor (M × N) (prodCoact (LinearMap.inr R M N n)) := by
  rw [prodCoact_inr_apply]
  rw [← LinearMap.comp_apply (prodCoact.rTensor C), ← LinearMap.rTensor_comp,
    prodCoact_comp_inr, LinearMap.rTensor_comp]
  have h :
      TensorProduct.assoc R (M × N) C C
        ((LinearMap.rTensor C (LinearMap.rTensor C (LinearMap.inr R M N)) ∘ₗ
          LinearMap.rTensor C (coact (R := R) (C := C) (M := N))) (ρN n))
        = (LinearMap.inr R M N).rTensor (C ⊗[R] C)
          (TensorProduct.assoc R N C C
            ((coact (R := R) (C := C) (M := N)).rTensor C (ρN n))) := by
    simp only [LinearMap.comp_apply]
    simpa [LinearMap.rTensor] using
      (TensorProduct.map_map_assoc (LinearMap.inr R M N) LinearMap.id LinearMap.id
        ((coact (R := R) (C := C) (M := N)).rTensor C (ρN n))).symm
  rw [h, coassoc_apply]
  rw [← LinearMap.comp_apply (Coalgebra.comul.lTensor (M × N)),
    LinearMap.lTensor_comp_rTensor, ← LinearMap.comp_apply (LinearMap.rTensor (C ⊗[R] C) _),
    LinearMap.rTensor_comp_lTensor]

private theorem prodCounit_inl (m : M) :
    (Coalgebra.counit : C →ₗ[R] R).lTensor (M × N) (prodCoact (LinearMap.inl R M N m))
      = (LinearMap.inl R M N m) ⊗ₜ[R] (1 : R) := by
  rw [prodCoact_inl_apply]
  rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor, ← LinearMap.rTensor_comp_lTensor,
    LinearMap.comp_apply, lTensor_counit_coact]
  simp

private theorem prodCounit_inr (n : N) :
    (Coalgebra.counit : C →ₗ[R] R).lTensor (M × N) (prodCoact (LinearMap.inr R M N n))
      = (LinearMap.inr R M N n) ⊗ₜ[R] (1 : R) := by
  rw [prodCoact_inr_apply]
  rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor, ← LinearMap.rTensor_comp_lTensor,
    LinearMap.comp_apply, lTensor_counit_coact]
  simp

omit [Coalgebra R C] [Comodule R C M] [Comodule R C N] in
/-- An element of `M × N` is the sum of its two summand inclusions. -/
private theorem prod_eq_inl_add_inr (m : M) (n : N) :
    (m, n) = LinearMap.inl R M N m + LinearMap.inr R M N n := by
  simp

/-- The product `M × N` of two right `C`-comodules, with the summandwise coaction. -/
noncomputable instance instProd : Comodule R C (M × N) where
  coact := prodCoact
  coassoc := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨m, n⟩ := x
    rw [prod_eq_inl_add_inr (R := R) m n]
    simp only [map_add, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    rw [prodCoassoc_inl, prodCoassoc_inr]
  lTensor_counit_comp_coact := by
    apply LinearMap.prod_ext
    · ext m
      simp only [LinearMap.comp_apply]
      rw [prodCounit_inl]
      rfl
    · ext n
      simp only [LinearMap.comp_apply]
      rw [prodCounit_inr]
      rfl

/-- The product coaction on a pair is the sum of the coactions included into each summand. -/
@[simp]
theorem prod_coact_apply (m : M) (n : N) :
    coact (R := R) (C := C) (M := M × N) (m, n) = (LinearMap.inl R M N).rTensor C (ρM m)
      + (LinearMap.inr R M N).rTensor C (ρN n) :=
  prodCoact_apply m n

/-- The product coaction on a first-summand inclusion is the included coaction of `M`. -/
@[simp]
theorem prod_coact_inl (m : M) :
    coact (R := R) (C := C) (M := M × N) (LinearMap.inl R M N m)
      = (LinearMap.inl R M N).rTensor C (ρM m) :=
  prodCoact_inl_apply m

/-- The product coaction on a second-summand inclusion is the included coaction of `N`. -/
@[simp]
theorem prod_coact_inr (n : N) :
    coact (R := R) (C := C) (M := M × N) (LinearMap.inr R M N n)
      = (LinearMap.inr R M N).rTensor C (ρN n) :=
  prodCoact_inr_apply n

namespace Hom

/-- The first projection `M × N → M` as a comodule morphism. -/
def fst : Hom R C (M × N) M where
  toLinearMap := LinearMap.fst R M N
  map_coact := by
    apply LinearMap.prod_ext
    · ext m
      simp
    · ext n
      simp

/-- The second projection `M × N → N` as a comodule morphism. -/
def snd : Hom R C (M × N) N where
  toLinearMap := LinearMap.snd R M N
  map_coact := by
    apply LinearMap.prod_ext
    · ext m
      simp
    · ext n
      simp

/-- The first inclusion `M → M × N` as a comodule morphism. -/
def inl : Hom R C M (M × N) where
  toLinearMap := LinearMap.inl R M N
  map_coact := (prodCoact_comp_inl).symm

/-- The second inclusion `N → M × N` as a comodule morphism. -/
def inr : Hom R C N (M × N) where
  toLinearMap := LinearMap.inr R M N
  map_coact := (prodCoact_comp_inr).symm

/-- The projection `fst` acts as the underlying first projection. -/
@[simp] theorem fst_apply (x : M × N) : (fst : Hom R C (M × N) M) x = x.1 := rfl
/-- The projection `snd` acts as the underlying second projection. -/
@[simp] theorem snd_apply (x : M × N) : (snd : Hom R C (M × N) N) x = x.2 := rfl
/-- The inclusion `inl` sends `m` to `(m, 0)`. -/
@[simp] theorem inl_apply (m : M) : (inl : Hom R C M (M × N)) m = (m, 0) := rfl
/-- The inclusion `inr` sends `n` to `(0, n)`. -/
@[simp] theorem inr_apply (n : N) : (inr : Hom R C N (M × N)) n = (0, n) := rfl

/-- The projection `fst` has the underlying first projection linear map. -/
@[simp]
theorem fst_toLinearMap : (fst : Hom R C (M × N) M).toLinearMap = LinearMap.fst R M N :=
  rfl

/-- The projection `snd` has the underlying second projection linear map. -/
@[simp]
theorem snd_toLinearMap : (snd : Hom R C (M × N) N).toLinearMap = LinearMap.snd R M N :=
  rfl

/-- The inclusion `inl` has the underlying first inclusion linear map. -/
@[simp]
theorem inl_toLinearMap : (inl : Hom R C M (M × N)).toLinearMap = LinearMap.inl R M N :=
  rfl

/-- The inclusion `inr` has the underlying second inclusion linear map. -/
@[simp]
theorem inr_toLinearMap : (inr : Hom R C N (M × N)).toLinearMap = LinearMap.inr R M N :=
  rfl

/-- The morphism into a product induced by a pair of morphisms. -/
def prod (f : Hom R C P M) (g : Hom R C P N) : Hom R C P (M × N) where
  toLinearMap := f.toLinearMap.prod g.toLinearMap
  map_coact := by
    have hdecomp : f.toLinearMap.prod g.toLinearMap
        = (LinearMap.inl R M N).comp f.toLinearMap
          + (LinearMap.inr R M N).comp g.toLinearMap := by ext q <;> simp
    refine LinearMap.ext fun p => ?_
    have hf := LinearMap.congr_fun f.map_coact p
    have hg := LinearMap.congr_fun g.map_coact p
    simp only [LinearMap.comp_apply] at hf hg
    -- Unfold the two compositions in `map_coact` to their pointwise form so the explicit
    -- `rTensor`/`TensorProduct.map` rewriting below applies; both sides are definitionally
    -- this application.
    change TensorProduct.map (f.toLinearMap.prod g.toLinearMap) LinearMap.id (coact p)
      = coact (R := R) (C := C) (M := M × N) ((f.toLinearMap.prod g.toLinearMap) p)
    rw [hdecomp, TensorProduct.map_add_left, LinearMap.add_apply,
      ← LinearMap.rTensor_map, ← LinearMap.rTensor_map, hf, hg]
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.coe_inl, LinearMap.coe_inr,
      Prod.mk_add_mk, add_zero, zero_add, prod_coact_apply]

/-- The morphism out of a coproduct induced by a pair of morphisms. -/
def coprod (f : Hom R C M P) (g : Hom R C N P) : Hom R C (M × N) P where
  toLinearMap := f.toLinearMap.coprod g.toLinearMap
  map_coact := by
    apply LinearMap.prod_ext
    · ext m
      have hf := LinearMap.congr_fun f.map_coact m
      simp only [LinearMap.comp_apply] at hf ⊢
      rw [prod_coact_inl, LinearMap.map_rTensor, LinearMap.coprod_inl, hf]
      congr 1
      simp only [LinearMap.coprod_apply, LinearMap.inl_apply, map_zero, add_zero]
    · ext n
      have hg := LinearMap.congr_fun g.map_coact n
      simp only [LinearMap.comp_apply] at hg ⊢
      rw [prod_coact_inr, LinearMap.map_rTensor, LinearMap.coprod_inr, hg]
      congr 1
      simp only [LinearMap.coprod_apply, LinearMap.inr_apply, map_zero, zero_add]

/-- The morphism into the product applies as the pair of its component morphisms. -/
@[simp] theorem prod_apply (f : Hom R C P M) (g : Hom R C P N) (p : P) :
    (prod f g) p = (f p, g p) := rfl

/-- The morphism out of the coproduct applies as the sum of its component morphisms. -/
@[simp] theorem coprod_apply (f : Hom R C M P) (g : Hom R C N P) (x : M × N) :
    (coprod f g) x = f x.1 + g x.2 := rfl

/-- The morphism into a product has the product of the underlying linear maps. -/
@[simp]
theorem prod_toLinearMap (f : Hom R C P M) (g : Hom R C P N) :
    (prod f g).toLinearMap = f.toLinearMap.prod g.toLinearMap :=
  rfl

/-- The morphism out of a coproduct has the coproduct of the underlying linear maps. -/
@[simp]
theorem coprod_toLinearMap (f : Hom R C M P) (g : Hom R C N P) :
    (coprod f g).toLinearMap = f.toLinearMap.coprod g.toLinearMap :=
  rfl

/-- The first projection recovers the first component of a morphism into the product. -/
@[simp] theorem fst_comp_prod (f : Hom R C P M) (g : Hom R C P N) :
    comp fst (prod f g) = f := by ext p; simp

/-- The second projection recovers the second component of a morphism into the product. -/
@[simp] theorem snd_comp_prod (f : Hom R C P M) (g : Hom R C P N) :
    comp snd (prod f g) = g := by ext p; simp

/-- The first inclusion recovers the first component of a morphism out of the coproduct. -/
@[simp] theorem coprod_comp_inl (f : Hom R C M P) (g : Hom R C N P) :
    comp (coprod f g) inl = f := by
  ext m
  simp only [comp_apply, coprod_apply, inl_apply]
  simp [Hom.apply_zero]

/-- The second inclusion recovers the second component of a morphism out of the coproduct. -/
@[simp] theorem coprod_comp_inr (f : Hom R C M P) (g : Hom R C N P) :
    comp (coprod f g) inr = g := by
  ext n
  simp only [comp_apply, coprod_apply, inr_apply]
  simp [Hom.apply_zero]

/-- A morphism into the product is determined by its two projections: two morphisms into
`M × N` that agree after `fst` and after `snd` are equal. This is the uniqueness half of the
product's universal property. -/
theorem prod_ext {h k : Hom R C P (M × N)} (hfst : comp fst h = comp fst k)
    (hsnd : comp snd h = comp snd k) : h = k :=
  Hom.ext fun p => Prod.ext (by simpa using congr($hfst p)) (by simpa using congr($hsnd p))

/-- A morphism out of the coproduct is determined by its two inclusions: two morphisms out of
`M × N` that agree after `inl` and after `inr` are equal. This is the uniqueness half of the
coproduct's universal property. -/
theorem coprod_ext {h k : Hom R C (M × N) P} (hinl : comp h inl = comp k inl)
    (hinr : comp h inr = comp k inr) : h = k := by
  ext x
  obtain ⟨m, n⟩ := x
  have hm := congr($hinl m)
  have hn := congr($hinr n)
  simp only [comp_apply, inl_apply, inr_apply] at hm hn
  have e1 : h (m, n) = h (m, 0) + h (0, n) := by
    simpa using map_add h.toLinearMap (m, 0) (0, n)
  have e2 : k (m, n) = k (m, 0) + k (0, n) := by
    simpa using map_add k.toLinearMap (m, 0) (0, n)
  rw [e1, e2, hm, hn]

/-- The first projection of the first inclusion is the identity. -/
@[simp] theorem fst_comp_inl : comp (fst : Hom R C (M × N) M) inl = id R C M := by
  ext m; simp

/-- The second projection kills the first inclusion. -/
@[simp] theorem snd_comp_inl : comp (snd : Hom R C (M × N) N) inl = 0 := by
  ext m; simp

/-- The first projection kills the second inclusion. -/
@[simp] theorem fst_comp_inr : comp (fst : Hom R C (M × N) M) inr = 0 := by
  ext n; simp

/-- The second projection of the second inclusion is the identity. -/
@[simp] theorem snd_comp_inr : comp (snd : Hom R C (M × N) N) inr = id R C N := by
  ext n; simp

/-- The two coproduct inclusions decompose the identity on the product comodule. -/
@[simp] theorem coprod_inl_inr : coprod (inl : Hom R C M (M × N)) inr = id R C (M × N) := by
  apply Hom.ext
  intro x
  obtain ⟨m, n⟩ := x
  simp

end Hom

end Comodule


end TauCeti
