/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.CentroidHom
public import Mathlib.CategoryTheory.Center.Preadditive
public import TauCeti.RingTheory.Idempotented.NondegMod
import TauCeti.CategoryTheory.Linear.FullSubcategory

/-!
# Bimodule endomorphisms act on nondegenerate modules

Let `H` be an idempotented algebra over a commutative ring `A`. A bimodule endomorphism of `H`,
that is an additive map `φ : H → H` with `φ(xy) = x φ(y) = φ(x) y` (Mathlib's centroid
`CentroidHom H`), acts on every nondegenerate module `M` by `m ↦ φ(e) • m`, for any `e ∈ H` with
`e • m = m`. The value does not depend on `e`: for a local unit `f` of `e` and `e'`,
`φ(e) • m = (φ(f) e) • m = φ(f) • m`, and likewise for `e'`. These actions commute with module
homomorphisms, so they form an element of the centre of the category `NondegMod A H`.

This gives a ring homomorphism `CentroidHom H →+* CatCenter (NondegMod A H)`
(`TauCeti.NondegMod.centroidToCatCenter`), defined for modules in every universe. For
`NondegMod.{max u₁ u₂} A H`, modules in a universe large enough to contain the regular module of
the unitization, it is injective, because on the nondegenerate part `H` of that regular module,
`φ` acts by `x ↦ φ(x)` (`TauCeti.NondegMod.centroidToCatCenter_injective`).

## Main definitions

* `CentroidHom.moduleEnd φ hM`: the action of `φ` on a nondegenerate module `M`.
* `TauCeti.NondegMod.centroidToCatCenter A H`: the ring homomorphism from the bimodule
  endomorphisms of `H` to the centre of `NondegMod A H`.

## Main results

* `CentroidHom.moduleEnd_apply_of_smul_eq`,
  `TauCeti.NondegMod.centroidToCatCenter_app_apply`: `φ` acts on `m` by `φ(e)` for every
  `e ∈ H` with `e • m = m`.
* `CentroidHom.moduleEnd_one`, `CentroidHom.moduleEnd_zero`, `CentroidHom.moduleEnd_add`,
  `CentroidHom.moduleEnd_mul`: the action respects the ring operations of `CentroidHom H`.
* `TauCeti.NondegMod.centroidToCatCenter_injective`: distinct bimodule endomorphisms act
  differently on nondegenerate modules in universe `max u₁ u₂`.

## References

* J. Bernstein, *Second adjointness for representations of reductive p-adic groups*, 1987
  manuscript, §1.1–1.2 and §1.8, pp. 3–4 and 8 (the centre of the category of nondegenerate
  modules and the bimodule endomorphisms of `H`).
-/

public section

universe v u₁ u₂

open CategoryTheory TauCeti

namespace CentroidHom

variable {A H : Type*} [CommSemiring A] [NonUnitalSemiring H] [Module A H]
  [IsScalarTower A H H] [SMulCommClass A H H] [IsIdempotented H]
  {M : Type*} [AddCommMonoid M] [Module (Unitization A H) M]

/-- A bimodule endomorphism `φ` of `H` gives the same action `φ(e) • m = φ(e') • m` through any
two elements `e, e'` of `H` fixing `m`: both equal `φ(f) • m` for a local unit `f` of `e` and
`e'`. -/
theorem inr_apply_smul_eq_of_smul_eq (φ : CentroidHom H) {m : M} {e e' : H}
    (he : (e : Unitization A H) • m = m) (he' : (e' : Unitization A H) • m = m) :
    (φ e : Unitization A H) • m = (φ e' : Unitization A H) • m := by
  classical
  obtain ⟨f, -, hf⟩ := IsIdempotented.exists_isIdempotentElem {e, e'}
  have key {e : H} (hfe : f * e = e) (he : (e : Unitization A H) • m = m) :
      (φ e : Unitization A H) • m = (φ f : Unitization A H) • m := by
    rw [← hfe, map_mul_right, Unitization.inr_mul, mul_smul, he]
  rw [key (hf e (by simp)).1 he, key (hf e' (by simp)).1 he']

/-- The underlying function of `CentroidHom.moduleEnd`: `m ↦ φ(e) • m` for a chosen local unit `e`
of `m`. -/
private noncomputable def moduleEndFun (φ : CentroidHom H) (hM : IsNondegenerate A H M) (m : M) :
    M :=
  (φ (isNondegenerate_iff.1 hM m).choose : Unitization A H) • m

private theorem moduleEndFun_eq_of_smul_eq (φ : CentroidHom H) (hM : IsNondegenerate A H M)
    {m : M} {e : H} (he : (e : Unitization A H) • m = m) :
    φ.moduleEndFun hM m = (φ e : Unitization A H) • m :=
  φ.inr_apply_smul_eq_of_smul_eq (isNondegenerate_iff.1 hM m).choose_spec.2 he

/-- The action `m ↦ φ(e) • m` of a bimodule endomorphism `φ` of `H` on a nondegenerate module
`M`, where `e ∈ H` is any element with `e • m = m` (`CentroidHom.moduleEnd_apply_of_smul_eq`). -/
noncomputable def moduleEnd (φ : CentroidHom H) (hM : IsNondegenerate A H M) :
    M →ₗ[Unitization A H] M := by
  classical
  let act : M →+ M :=
    { toFun := φ.moduleEndFun hM
      map_zero' := by rw [moduleEndFun, smul_zero]
      map_add' m m' := by
        obtain ⟨f, -, hf⟩ := hM.exists_isIdempotentElem_forall_smul_eq {m, m'}
        rw [φ.moduleEndFun_eq_of_smul_eq hM (by rw [smul_add, hf m (by simp), hf m' (by simp)]),
          φ.moduleEndFun_eq_of_smul_eq hM (hf m (by simp)),
          φ.moduleEndFun_eq_of_smul_eq hM (hf m' (by simp)), smul_add] }
  refine
    { toFun := act
      map_add' := act.map_add
      map_smul' := hM.map_smul_of_map_inr_smul act fun h m ↦ ?_ }
  -- Take a two-sided local unit `f` of `h` and of a local unit `e` of `m`; then `f` fixes `m` and
  -- `h • m`, and both sides are `φ(h) • m`.
  obtain ⟨e, -, he⟩ := isNondegenerate_iff.1 hM m
  obtain ⟨f, -, hf⟩ := IsIdempotented.exists_isIdempotentElem {h, e}
  have hfm : (f : Unitization A H) • m = m := inr_smul_eq_of_mul_eq he (hf e (by simp)).1
  have hfhm : (f : Unitization A H) • (h : Unitization A H) • m = (h : Unitization A H) • m := by
    rw [smul_smul, ← Unitization.inr_mul, (hf h (by simp)).1]
  have hact {x : M} (hx : (f : Unitization A H) • x = x) : act x = (φ f : Unitization A H) • x :=
    φ.moduleEndFun_eq_of_smul_eq hM hx
  rw [hact hfhm, hact hfm, smul_smul, smul_smul, ← Unitization.inr_mul, ← Unitization.inr_mul,
    ← map_mul_right, ← map_mul_left, (hf h (by simp)).1, (hf h (by simp)).2]

/-- A bimodule endomorphism `φ` acts on `m` by `φ(e)`, for any `e ∈ H` with `e • m = m`. -/
theorem moduleEnd_apply_of_smul_eq (φ : CentroidHom H) (hM : IsNondegenerate A H M) {m : M}
    {e : H} (he : (e : Unitization A H) • m = m) :
    φ.moduleEnd hM m = (φ e : Unitization A H) • m :=
  φ.moduleEndFun_eq_of_smul_eq hM he

/-- A bimodule endomorphism commutes with homomorphisms of nondegenerate modules. -/
theorem moduleEnd_comp {N : Type*} [AddCommMonoid N] [Module (Unitization A H) N]
    (φ : CentroidHom H) (hM : IsNondegenerate A H M) (hN : IsNondegenerate A H N)
    (g : M →ₗ[Unitization A H] N) :
    φ.moduleEnd hN ∘ₗ g = g ∘ₗ φ.moduleEnd hM := by
  ext m
  obtain ⟨e, -, he⟩ := isNondegenerate_iff.1 hM m
  have hge : (e : Unitization A H) • g m = g m := by rw [← map_smul, he]
  simp only [LinearMap.comp_apply]
  rw [φ.moduleEnd_apply_of_smul_eq hN hge, φ.moduleEnd_apply_of_smul_eq hM he, map_smul]

variable (hM : IsNondegenerate A H M)

/-- The identity bimodule endomorphism acts as the identity. -/
@[simp]
theorem moduleEnd_one : (1 : CentroidHom H).moduleEnd hM = LinearMap.id := by
  ext m
  obtain ⟨e, -, he⟩ := isNondegenerate_iff.1 hM m
  rw [moduleEnd_apply_of_smul_eq _ hM he, CentroidHom.one_apply, he, LinearMap.id_apply]

/-- The zero bimodule endomorphism acts as zero. -/
@[simp]
theorem moduleEnd_zero : (0 : CentroidHom H).moduleEnd hM = 0 := by
  ext m
  obtain ⟨e, -, he⟩ := isNondegenerate_iff.1 hM m
  rw [moduleEnd_apply_of_smul_eq _ hM he, CentroidHom.zero_apply, Unitization.inr_zero, zero_smul,
    LinearMap.zero_apply]

/-- The action of a sum of bimodule endomorphisms is the sum of their actions. -/
@[simp]
theorem moduleEnd_add (φ ψ : CentroidHom H) :
    (φ + ψ).moduleEnd hM = φ.moduleEnd hM + ψ.moduleEnd hM := by
  ext m
  obtain ⟨e, -, he⟩ := isNondegenerate_iff.1 hM m
  rw [LinearMap.add_apply, moduleEnd_apply_of_smul_eq _ hM he, moduleEnd_apply_of_smul_eq _ hM he,
    moduleEnd_apply_of_smul_eq _ hM he, CentroidHom.add_apply, Unitization.inr_add, add_smul]

/-- The action of a composite of bimodule endomorphisms is the composite of their actions. -/
@[simp]
theorem moduleEnd_mul (φ ψ : CentroidHom H) :
    (φ * ψ).moduleEnd hM = φ.moduleEnd hM ∘ₗ ψ.moduleEnd hM := by
  classical
  ext m
  obtain ⟨e, -, he⟩ := isNondegenerate_iff.1 hM m
  -- A local unit `f` of `ψ(e)` fixes `ψ(e) • m`, and `φ(f) ψ(e) = φ(f ψ(e)) = φ(ψ(e))`.
  obtain ⟨f, -, hf⟩ := IsIdempotented.exists_isIdempotentElem {ψ e}
  have hfψ : f * ψ e = ψ e := (hf (ψ e) (by simp)).1
  have hfm :
      (f : Unitization A H) • (ψ e : Unitization A H) • m = (ψ e : Unitization A H) • m := by
    rw [smul_smul, ← Unitization.inr_mul, hfψ]
  rw [LinearMap.comp_apply, moduleEnd_apply_of_smul_eq _ hM he, moduleEnd_apply_of_smul_eq _ hM he,
    moduleEnd_apply_of_smul_eq _ hM hfm, smul_smul, ← Unitization.inr_mul, ← map_mul_right, hfψ,
    CentroidHom.mul_apply]

end CentroidHom

namespace TauCeti.NondegMod

variable {A : Type u₁} {H : Type u₂} [CommRing A] [NonUnitalRing H] [Module A H]
  [IsScalarTower A H H] [SMulCommClass A H H] [IsIdempotented H]

variable (A H)

/-- The element of the centre of `NondegMod A H` given by a bimodule endomorphism `φ` of `H`,
acting on each nondegenerate module `M` by `m ↦ φ(e) • m` for a local unit `e` of `m`. -/
private noncomputable def centroidToCatCenterAux (φ : CentroidHom H) :
    CatCenter (NondegMod.{v} A H) :=
  .of
    { app M := ObjectProperty.homMk
        (ModuleCat.ofHom (φ.moduleEnd M.isNondegenerate))
      naturality M N g := by
        ext m
        -- Both sides reduce to the two composites in `CentroidHom.moduleEnd_comp`.
        simpa using LinearMap.congr_fun
          (φ.moduleEnd_comp M.isNondegenerate N.isNondegenerate g.hom.hom) m }

variable {A H} in
private theorem centroidToCatCenterAux_app_hom_hom (φ : CentroidHom H) (M : NondegMod.{v} A H) :
    ((centroidToCatCenterAux.{v} A H φ).app M).hom.hom = φ.moduleEnd M.isNondegenerate :=
  rfl

/-- **Bimodule endomorphisms of `H` give central endomorphisms of nondegenerate modules.** The
ring homomorphism from the centroid of `H` to the centre of `NondegMod A H`, sending `φ` to the
natural transformation `m ↦ φ(e) • m` (`e` a local unit of `m`). -/
noncomputable def centroidToCatCenter : CentroidHom H →+* CatCenter (NondegMod.{v} A H) where
  toFun := centroidToCatCenterAux.{v} A H
  map_one' := by
    ext M m
    simp [centroidToCatCenterAux_app_hom_hom]
  map_mul' φ ψ := by
    ext M m
    simp [CatCenter.mul_app', centroidToCatCenterAux_app_hom_hom]
  map_zero' := by
    ext M m
    simp [centroidToCatCenterAux_app_hom_hom]
  map_add' φ ψ := by
    ext M m
    simp [centroidToCatCenterAux_app_hom_hom]

variable {A H}

/-- A bimodule endomorphism `φ` acts on a nondegenerate module `M` by `φ.moduleEnd`. -/
@[simp]
theorem centroidToCatCenter_app_hom_hom (φ : CentroidHom H) (M : NondegMod.{v} A H) :
    ((centroidToCatCenter.{v} A H φ).app M).hom.hom = φ.moduleEnd M.isNondegenerate :=
  (rfl)

/-- A bimodule endomorphism `φ` acts on an element `m` of a nondegenerate module by `φ(e)`, for any
`e ∈ H` with `e • m = m`. -/
theorem centroidToCatCenter_app_apply (φ : CentroidHom H) (M : NondegMod.{v} A H) {m : M.obj}
    {e : H} (he : (e : Unitization A H) • m = m) :
    ((centroidToCatCenter.{v} A H φ).app M).hom.hom m = (φ e : Unitization A H) • m :=
  φ.moduleEnd_apply_of_smul_eq M.isNondegenerate he

/-- **Distinct bimodule endomorphisms act differently** on nondegenerate modules in universe
`max u₁ u₂`, large enough to contain the regular module of the unitization: on its nondegenerate
part `H`, `φ` acts by `x ↦ φ(x)`. -/
theorem centroidToCatCenter_injective :
    Function.Injective (centroidToCatCenter.{max u₁ u₂} A H) := by
  classical
  intro φ ψ h
  ext x
  obtain ⟨e, -, he⟩ := IsIdempotented.exists_isIdempotentElem {x}
  have hex : e * x = x := (he x (by simp)).1
  let X := (nondegeneratePartFunctor.{max u₁ u₂} A H).obj (ModuleCat.of _ (Unitization A H))
  have hx : (x : Unitization A H) ∈ nondegeneratePart A H (Unitization A H) := by
    simpa [← Unitization.inr_mul, hex] using
      inr_smul_mem_nondegeneratePart (A := A) e (x : Unitization A H)
  let m : nondegeneratePart A H (Unitization A H) := ⟨x, hx⟩
  have hm : (e : Unitization A H) • (m : X.obj) = m := by
    refine Subtype.ext ?_
    rw [Submodule.coe_smul, smul_eq_mul, ← Unitization.inr_mul, hex]
  have := congrArg (fun z : CatCenter (NondegMod.{max u₁ u₂} A H) ↦
    ((z.app X).hom.hom m).val) h
  simp only [centroidToCatCenter_app_apply _ X hm] at this
  -- The action on `X.obj` is that of the submodule `H • (A ⊕ H)` only after unfolding
  -- `nondegeneratePartFunctor` inside the instance, so `Submodule.coe_smul` cannot rewrite it;
  -- by definition both sides are the products `φ(e) x` and `ψ(e) x` in the unitization.
  replace this : (φ e : Unitization A H) * x = (ψ e : Unitization A H) * x := this
  rwa [← Unitization.inr_mul, ← Unitization.inr_mul, ← map_mul_right, ← map_mul_right, hex,
    Unitization.inr_injective.eq_iff] at this

end TauCeti.NondegMod
