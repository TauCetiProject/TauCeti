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
# Bimodule endomorphisms form the centre of nondegenerate modules

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
`φ` acts by `x ↦ φ(x)` (`TauCeti.NondegMod.centroidToCatCenter_injective`). It is also
surjective, so it is a ring isomorphism (`TauCeti.NondegMod.centroidEquivCatCenter`): a central
`z` acts on the regular module `H • (A ⊕ H)`, whose elements are those of `H`, by a map `φ` that
is left `H`-linear and, by naturality for right multiplications, right `H`-linear; naturality for
the maps `u ↦ u • m` shows that `z` acts on `m` by `φ(e)` for a local unit `e` of `m`.

## Main definitions

* `CentroidHom.moduleEnd φ hM`: the action of `φ` on a nondegenerate module `M`.
* `TauCeti.NondegMod.centroidToCatCenter A H`: the ring homomorphism from the bimodule
  endomorphisms of `H` to the centre of `NondegMod A H`.
* `TauCeti.NondegMod.centroidEquivCatCenter A H`: the ring isomorphism
  `CentroidHom H ≃+* CatCenter (NondegMod A H)` for modules in universe `max u₁ u₂`.

## Main results

* `CentroidHom.moduleEnd_apply_of_smul_eq`,
  `TauCeti.NondegMod.centroidToCatCenter_app_apply`: `φ` acts on `m` by `φ(e)` for every
  `e ∈ H` with `e • m = m`.
* `CentroidHom.moduleEnd_one`, `CentroidHom.moduleEnd_zero`, `CentroidHom.moduleEnd_add`,
  `CentroidHom.moduleEnd_mul`: the action respects the ring operations of `CentroidHom H`.
* `TauCeti.NondegMod.centroidToCatCenter_injective`: distinct bimodule endomorphisms act
  differently on nondegenerate modules in universe `max u₁ u₂`.
* `TauCeti.NondegMod.centroidToCatCenter_surjective`: every element of the centre of
  `NondegMod A H` (universe `max u₁ u₂`) comes from a bimodule endomorphism of `H`.

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

/-- The regular nondegenerate module `H • (A ⊕ H)`: the nondegenerate part of the unitization,
whose elements are those of `H` (`TauCeti.inr_snd_eq_of_mem_nondegeneratePart`). -/
private noncomputable abbrev regular : NondegMod.{max u₁ u₂} A H :=
  (nondegeneratePartFunctor.{max u₁ u₂} A H).obj (ModuleCat.of _ (Unitization A H))

/-! The module operations of `regular` are those of the submodule `H • (A ⊕ H)` only after
unfolding `nondegeneratePartFunctor` inside the instances, so `Submodule.coe_zero`,
`Submodule.coe_add` and `Submodule.coe_smul` cannot rewrite them. The following lemmas state these
definitional equalities once. -/

private theorem regular_val_zero : (0 : (regular (A := A) (H := H)).obj).val = 0 :=
  rfl

private theorem regular_val_add (u v : (regular (A := A) (H := H)).obj) :
    (u + v).val = u.val + v.val :=
  rfl

private theorem regular_val_smul (r : Unitization A H) (u : (regular (A := A) (H := H)).obj) :
    (r • u).val = r * u.val :=
  rfl

/-- An element `h ∈ H`, as an element of the regular nondegenerate module. -/
private noncomputable def regularElem (h : H) : (regular (A := A) (H := H)).obj :=
  ⟨(h : Unitization A H), by
    classical
    obtain ⟨e, -, heh⟩ := IsIdempotented.exists_isIdempotentElem {h}
    simpa [← Unitization.inr_mul, (heh h (by simp)).1] using
      inr_smul_mem_nondegeneratePart (A := A) e (h : Unitization A H)⟩

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
  have hm : (e : Unitization A H) • regularElem (A := A) x = regularElem x := by
    refine Subtype.ext ?_
    rw [regular_val_smul, regularElem, ← Unitization.inr_mul, hex]
  have := congrArg (fun z : CatCenter (NondegMod.{max u₁ u₂} A H) ↦
    ((z.app regular).hom.hom (regularElem x)).val) h
  simp only [centroidToCatCenter_app_apply _ regular hm] at this
  rw [regular_val_smul, regular_val_smul, regularElem, ← Unitization.inr_mul,
    ← Unitization.inr_mul, ← map_mul_right, ← map_mul_right, hex] at this
  exact Unitization.inr_injective this

/-! ### The centre is the centroid -/

/-- Right multiplication by `y ∈ H`, an endomorphism of the regular nondegenerate module. -/
private noncomputable def regularMulRight (y : H) :
    regular (A := A) (H := H) ⟶ regular (A := A) (H := H) :=
  (nondegeneratePartFunctor.{max u₁ u₂} A H).map
    (ModuleCat.ofHom (LinearMap.toSpanSingleton (Unitization A H) (Unitization A H) y))

/-- The morphism `u ↦ u • m` from the regular nondegenerate module to a nondegenerate module. -/
private noncomputable def regularToSpan (M : NondegMod.{max u₁ u₂} A H) (m : M.obj) :
    regular (A := A) (H := H) ⟶ M :=
  ObjectProperty.homMk (ModuleCat.ofHom
    (LinearMap.toSpanSingleton (Unitization A H) M.obj m ∘ₗ
      (nondegeneratePart A H (Unitization A H)).subtype))

/-- `regularMulRight y` multiplies on the right by `y`; this holds by unfolding
`nondegeneratePartFunctor.map`, which `simp` cannot see through. -/
private theorem regularMulRight_val (y : H) (u : (regular (A := A) (H := H)).obj) :
    ((regularMulRight y).hom.hom u).val = u.val * y :=
  rfl

/-- `regularToSpan M m` acts by `u ↦ u • m`, by definition. -/
private theorem regularToSpan_apply (M : NondegMod.{max u₁ u₂} A H) (m : M.obj)
    (u : (regular (A := A) (H := H)).obj) :
    (regularToSpan M m).hom.hom u = u.val • m :=
  rfl

private theorem regularElem_zero : regularElem (A := A) (0 : H) = 0 :=
  Subtype.ext (Unitization.inr_zero A)

private theorem regularElem_add (x y : H) :
    regularElem (A := A) (x + y) = regularElem x + regularElem y :=
  Subtype.ext (Unitization.inr_add A x y)

private theorem regularElem_mul_eq_smul (x y : H) :
    regularElem (A := A) (x * y) = (x : Unitization A H) • regularElem y :=
  Subtype.ext (Unitization.inr_mul A x y)

private theorem regularElem_mul_eq_mulRight (x y : H) :
    regularElem (A := A) (x * y) = (regularMulRight y).hom.hom (regularElem x) :=
  Subtype.ext (Unitization.inr_mul A x y)

private theorem regularToSpan_regularElem (M : NondegMod.{max u₁ u₂} A H) (m : M.obj) (h : H) :
    (regularToSpan M m).hom.hom (regularElem h) = (h : Unitization A H) • m :=
  regularToSpan_apply M m _

omit [IsIdempotented H] in
/-- An element of the centre commutes with every morphism, elementwise. -/
private theorem catCenter_app_hom_apply (z : CatCenter (NondegMod.{v} A H))
    {X Y : NondegMod.{v} A H} (f : X ⟶ Y) (x : X.obj) :
    (z.app Y).hom.hom (f.hom.hom x) = f.hom.hom ((z.app X).hom.hom x) := by
  simpa using congr(($(z.naturality f)).hom.hom x)

variable (A H) in
/-- The function `H → H` given by an element `z` of the centre: `z` acting on `h ∈ H` in the
regular nondegenerate module. -/
private noncomputable def catCenterToFun (z : CatCenter (NondegMod.{max u₁ u₂} A H)) (h : H) :
    H :=
  ((z.app regular).hom.hom (regularElem h)).val.snd

private theorem inr_catCenterToFun (z : CatCenter (NondegMod.{max u₁ u₂} A H)) (h : H) :
    (catCenterToFun A H z h : Unitization A H) =
      ((z.app regular).hom.hom (regularElem h)).val :=
  inr_snd_eq_of_mem_nondegeneratePart ((z.app regular).hom.hom (regularElem h)).property

/-- The bimodule endomorphism of `H` given by an element of the centre of `NondegMod A H`. -/
private noncomputable def catCenterToCentroid (z : CatCenter (NondegMod.{max u₁ u₂} A H)) :
    CentroidHom H where
  toFun := catCenterToFun A H z
  map_zero' := Unitization.inr_injective (R := A) <| by
    rw [inr_catCenterToFun, regularElem_zero, map_zero, Unitization.inr_zero, regular_val_zero]
  map_add' x y := Unitization.inr_injective (R := A) <| by
    rw [Unitization.inr_add, inr_catCenterToFun, inr_catCenterToFun, inr_catCenterToFun,
      regularElem_add, map_add, regular_val_add]
  map_mul_left' x y := Unitization.inr_injective (R := A) <| by
    rw [Unitization.inr_mul, inr_catCenterToFun, inr_catCenterToFun, regularElem_mul_eq_smul,
      map_smul, regular_val_smul]
  map_mul_right' x y := Unitization.inr_injective (R := A) <| by
    rw [Unitization.inr_mul, inr_catCenterToFun, inr_catCenterToFun, regularElem_mul_eq_mulRight,
      catCenter_app_hom_apply, regularMulRight_val]

/-- `catCenterToCentroid z` is `catCenterToFun A H z`, by definition. -/
private theorem catCenterToCentroid_apply (z : CatCenter (NondegMod.{max u₁ u₂} A H)) (h : H) :
    catCenterToCentroid z h = catCenterToFun A H z h :=
  rfl

/-- **The centre of `NondegMod A H` is the centroid of `H`**: every central endomorphism of
the identity functor of nondegenerate modules in universe `max u₁ u₂` comes from a bimodule
endomorphism of `H`, namely its action on the regular nondegenerate module `H • (A ⊕ H)`. -/
theorem centroidToCatCenter_surjective :
    Function.Surjective (centroidToCatCenter.{max u₁ u₂} A H) := by
  intro z
  refine ⟨catCenterToCentroid z, ?_⟩
  ext M m
  obtain ⟨e, -, he⟩ := isNondegenerate_iff.1 M.isNondegenerate m
  rw [centroidToCatCenter_app_apply _ M he]
  conv_rhs => rw [← he, ← regularToSpan_regularElem, catCenter_app_hom_apply]
  rw [catCenterToCentroid_apply, regularToSpan_apply, inr_catCenterToFun]

variable (A H) in
/-- **The centre of the category of nondegenerate modules** is the ring of bimodule
endomorphisms of `H`: `CentroidHom H ≃+* CatCenter (NondegMod A H)`. -/
noncomputable def centroidEquivCatCenter :
    CentroidHom H ≃+* CatCenter (NondegMod.{max u₁ u₂} A H) :=
  RingEquiv.ofBijective (centroidToCatCenter.{max u₁ u₂} A H)
    ⟨centroidToCatCenter_injective, centroidToCatCenter_surjective⟩

@[simp]
theorem centroidEquivCatCenter_apply (φ : CentroidHom H) :
    centroidEquivCatCenter A H φ = centroidToCatCenter.{max u₁ u₂} A H φ :=
  RingEquiv.ofBijective_apply _ _ _

end TauCeti.NondegMod
