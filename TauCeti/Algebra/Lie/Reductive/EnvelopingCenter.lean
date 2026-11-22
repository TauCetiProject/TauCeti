/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Reductive.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Functoriality
public import TauCeti.Algebra.Lie.UniversalEnveloping.ProductCenter
public import Mathlib.Algebra.Lie.Prod
import Mathlib.LinearAlgebra.Projection

/-!
# The enveloping algebra and its center for a reductive Lie algebra

Two complementary ideals `I` and `J` of a Lie algebra bracket to zero against each other, so
addition `I × J → L` is an equivalence of Lie algebras (`LieIdeal.prodEquivOfIsCompl`). For a
finite-dimensional reductive Lie algebra `L` over a field of characteristic zero, the centre and
the derived ideal are complementary (`TauCeti.isCompl_center_derivedSeries`), which gives the
central/derived splitting `L ≃ z(L) × [L, L]` (`TauCeti.centerDerivedEquiv`).

Transporting the product comparison `TauCeti.UniversalEnvelopingAlgebra.productEnveloping`
through this splitting gives the algebra equivalence

`U(L) ≃ Sym(z(L)) ⊗ U([L, L])`  (`TauCeti.UniversalEnvelopingAlgebra.reductiveEnveloping`),

which sends a canonical generator `x` to `ι_z(pr_z x) ⊗ 1 + 1 ⊗ ι_der(pr_der x)`, and whose
inverse multiplies the images of the two factor inclusions. Its restriction to the centers is the
algebra equivalence

`Z(U(L)) ≃ Sym(z(L)) ⊗ Z(U([L, L]))`  (`TauCeti.UniversalEnvelopingAlgebra.reductiveCenterEquiv`),

which, followed by `id ⊗ (Z(U([L, L])) ↪ U([L, L]))`, is `reductiveEnveloping` on the underlying
central element. Both are built from universal properties: no Harish-Chandra theorem is used.

## Main definitions

* `LieIdeal.prodEquivOfIsCompl`: addition `I × J ≃ₗ⁅R⁆ L` for complementary ideals.
* `TauCeti.centerDerivedEquiv`: the splitting `L ≃ₗ⁅K⁆ z(L) × [L, L]` of a reductive `L`.
* `TauCeti.UniversalEnvelopingAlgebra.reductiveEnveloping`: `U(L) ≃ₐ[K] Sym(z(L)) ⊗ U([L, L])`.
* `TauCeti.UniversalEnvelopingAlgebra.reductiveCenterEquiv`:
  `Z(U(L)) ≃ₐ[K] Sym(z(L)) ⊗ Z(U([L, L]))`.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.reductiveEnveloping_ι`: the value on a generator.
* `TauCeti.UniversalEnvelopingAlgebra.reductiveEnveloping_symm_tmul`: the inverse on a pure tensor.
* `TauCeti.UniversalEnvelopingAlgebra.reductiveEnveloping_naturality`: naturality for Lie maps
  sending the centre into the centre.
* `TauCeti.UniversalEnvelopingAlgebra.reductiveCenterEquiv_inclusion`: the inclusion square.
* `TauCeti.UniversalEnvelopingAlgebra.reductiveCenterEquiv_symm_tmul`: the pure-tensor formula.

## References

* J. Dixmier, *Enveloping Algebras*, §1.6.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §19.1.
-/

public section

open scoped TensorProduct

open LieAlgebra

universe u v w

namespace LieIdeal

variable {R : Type u} {L : Type v} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- Elements of two complementary ideals bracket to zero. -/
theorem lie_eq_zero_of_isCompl {I J : LieIdeal R L} (h : IsCompl I J) {x y : L} (hx : x ∈ I)
    (hy : y ∈ J) : ⁅x, y⁆ = 0 := by
  have hm : ⁅x, y⁆ ∈ I ⊓ J :=
    ⟨by rw [← lie_skew]; exact I.neg_mem (I.lie_mem hx), J.lie_mem hy⟩
  rw [h.inf_eq_bot] at hm
  exact (LieSubmodule.mem_bot _).mp hm

/-- For complementary ideals `I` and `J` of a Lie algebra `L`, addition `I × J → L` is an
equivalence of Lie algebras: the cross brackets vanish because they lie in `I ⊓ J = ⊥`. -/
noncomputable def prodEquivOfIsCompl (I J : LieIdeal R L) (h : IsCompl I J) :
    (I × J) ≃ₗ⁅R⁆ L :=
  { Submodule.prodEquivOfIsCompl I.toSubmodule J.toSubmodule
      (LieSubmodule.isCompl_toSubmodule.mpr h) with
    map_lie' := by
      rintro ⟨a, b⟩ ⟨c, d⟩
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
        Submodule.coe_prodEquivOfIsCompl', LieAlgebra.Prod.bracket_apply, lie_add, add_lie,
        lie_eq_zero_of_isCompl h a.property d.property,
        lie_eq_zero_of_isCompl h.symm b.property c.property]
      abel }

/-- `prodEquivOfIsCompl` is addition. -/
@[simp]
theorem prodEquivOfIsCompl_apply (I J : LieIdeal R L) (h : IsCompl I J) (p : I × J) :
    prodEquivOfIsCompl I J h p = (p.1 : L) + p.2 :=
  (rfl)

/-- The inverse of `prodEquivOfIsCompl` on an element of the first ideal. -/
@[simp]
theorem prodEquivOfIsCompl_symm_apply_left (I J : LieIdeal R L) (h : IsCompl I J) (x : I) :
    (prodEquivOfIsCompl I J h).symm x = (x, 0) :=
  (prodEquivOfIsCompl I J h).symm_apply_eq.2 <| by simp

/-- The inverse of `prodEquivOfIsCompl` on an element of the second ideal. -/
@[simp]
theorem prodEquivOfIsCompl_symm_apply_right (I J : LieIdeal R L) (h : IsCompl I J) (x : J) :
    (prodEquivOfIsCompl I J h).symm x = (0, x) :=
  (prodEquivOfIsCompl I J h).symm_apply_eq.2 <| by simp

end LieIdeal

namespace TauCeti

section Splitting

variable (K : Type u) (L : Type v) [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [HasCentralRadical K L]

/-- The central/derived splitting `L ≃ z(L) × [L, L]` of a finite-dimensional reductive Lie
algebra over a field of characteristic zero: the inverse of addition. -/
noncomputable def centerDerivedEquiv : L ≃ₗ⁅K⁆ (center K L) × derivedSeries K L 1 :=
  (LieIdeal.prodEquivOfIsCompl _ _ (isCompl_center_derivedSeries K L)).symm

/-- The inverse of the central/derived splitting is addition. -/
@[simp]
theorem centerDerivedEquiv_symm_apply (p : (center K L) × derivedSeries K L 1) :
    (centerDerivedEquiv K L).symm p = (p.1 : L) + p.2 :=
  (rfl)

/-- The two components of the central/derived splitting add up to the original element. -/
theorem centerDerivedEquiv_fst_add_snd (x : L) :
    ((centerDerivedEquiv K L x).1 : L) + (centerDerivedEquiv K L x).2 = x := by
  rw [← centerDerivedEquiv_symm_apply, LieEquiv.symm_apply_apply]

/-- The central/derived splitting of a central element. -/
@[simp]
theorem centerDerivedEquiv_center (z : center K L) :
    centerDerivedEquiv K L z = (z, 0) :=
  LieIdeal.prodEquivOfIsCompl_symm_apply_left _ _ _ z

/-- The central/derived splitting of an element of the derived ideal. -/
@[simp]
theorem centerDerivedEquiv_derivedSeries (d : derivedSeries K L 1) :
    centerDerivedEquiv K L d = (0, d) :=
  LieIdeal.prodEquivOfIsCompl_symm_apply_right _ _ _ d

/-- The splitting composed with the inclusion of the centre is the first factor inclusion. -/
theorem centerDerivedEquiv_comp_incl_center :
    (centerDerivedEquiv K L).toLieHom.comp (center K L).incl =
      LieHom.inl K (center K L) (derivedSeries K L 1) := by
  ext z <;> simp

/-- The splitting composed with the inclusion of the derived ideal is the second factor
inclusion. -/
theorem centerDerivedEquiv_comp_incl_derivedSeries :
    (centerDerivedEquiv K L).toLieHom.comp (derivedSeries K L 1).incl =
      LieHom.inr K (center K L) (derivedSeries K L 1) := by
  ext d <;> simp

end Splitting

section Restrict

variable {K : Type u} {L : Type v} {L' : Type w} [CommRing K] [LieRing L] [LieAlgebra K L]
  [LieRing L'] [LieAlgebra K L']

/-- A Lie homomorphism sending the centre into the centre, restricted to the centres. -/
def centerRestrict (f : L →ₗ⁅K⁆ L') (hf : ∀ z ∈ center K L, f z ∈ center K L') :
    center K L →ₗ⁅K⁆ center K L' where
  toLinearMap := f.toLinearMap.restrict hf
  map_lie' {x y} := Subtype.ext (f.map_lie x y)

/-- `centerRestrict` is `f` on the underlying elements. -/
@[simp]
theorem coe_centerRestrict_apply (f : L →ₗ⁅K⁆ L') (hf : ∀ z ∈ center K L, f z ∈ center K L')
    (z : center K L) : (centerRestrict f hf z : L') = f z :=
  (rfl)

/-- A Lie homomorphism restricted to the derived ideals. -/
def derivedSeriesRestrict (f : L →ₗ⁅K⁆ L') :
    derivedSeries K L 1 →ₗ⁅K⁆ derivedSeries K L' 1 where
  toLinearMap := f.toLinearMap.restrict fun _ hx =>
    LieIdeal.derivedSeries_map_le (f := f) 1 (LieIdeal.mem_map hx)
  map_lie' {x y} := Subtype.ext (f.map_lie x y)

/-- `derivedSeriesRestrict` is `f` on the underlying elements. -/
@[simp]
theorem coe_derivedSeriesRestrict_apply (f : L →ₗ⁅K⁆ L') (d : derivedSeries K L 1) :
    (derivedSeriesRestrict f d : L') = f d :=
  (rfl)

end Restrict

section Naturality

variable {K : Type u} {L : Type v} {L' : Type w} [Field K] [CharZero K] [LieRing L]
  [LieAlgebra K L] [FiniteDimensional K L] [HasCentralRadical K L] [LieRing L']
  [LieAlgebra K L'] [FiniteDimensional K L'] [HasCentralRadical K L']

/-- The central/derived splitting is natural for Lie maps sending the centre into the centre. -/
theorem centerDerivedEquiv_map (f : L →ₗ⁅K⁆ L') (hf : ∀ z ∈ center K L, f z ∈ center K L')
    (x : L) :
    centerDerivedEquiv K L' (f x) =
      (centerRestrict f hf (centerDerivedEquiv K L x).1,
        derivedSeriesRestrict f (centerDerivedEquiv K L x).2) := by
  have h := centerDerivedEquiv_symm_apply K L'
    (centerRestrict f hf (centerDerivedEquiv K L x).1,
      derivedSeriesRestrict f (centerDerivedEquiv K L x).2)
  rw [coe_centerRestrict_apply, coe_derivedSeriesRestrict_apply, ← map_add,
    centerDerivedEquiv_fst_add_snd] at h
  rw [← h, LieEquiv.apply_symm_apply]

end Naturality

namespace UniversalEnvelopingAlgebra

private theorem mapEquiv_map {R L M N : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [LieRing M] [LieAlgebra R M] [LieRing N] [LieAlgebra R N] (e : M ≃ₗ⁅R⁆ N)
    (g : L →ₗ⁅R⁆ M) (a : _root_.UniversalEnvelopingAlgebra R L) :
    mapEquiv R e (map R g a) = map R (e.toLieHom.comp g) a := by
  rw [map_comp, AlgHom.comp_apply, ← mapEquiv_toAlgHom, AlgEquiv.toAlgHom_apply]

section Enveloping

variable (K : Type u) (L : Type v) [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [HasCentralRadical K L]

local notation "UL" => _root_.UniversalEnvelopingAlgebra K L
local notation "UD" => _root_.UniversalEnvelopingAlgebra K (derivedSeries K L 1)
local notation "SZ" => SymmetricAlgebra K (center K L)

/-- The enveloping algebra of a reductive Lie algebra: `U(L) ≃ Sym(z(L)) ⊗ U([L, L])`, the map
induced by the central/derived splitting followed by `productEnveloping`. -/
noncomputable def reductiveEnveloping : UL ≃ₐ[K] SZ ⊗[K] UD :=
  (mapEquiv K (centerDerivedEquiv K L)).trans
    (productEnveloping K (center K L) (derivedSeries K L 1))

/-- The definition of `reductiveEnveloping`, for use outside this module. -/
theorem reductiveEnveloping_def :
    reductiveEnveloping K L =
      (mapEquiv K (centerDerivedEquiv K L)).trans
        (productEnveloping K (center K L) (derivedSeries K L 1)) :=
  (rfl)

/-- `reductiveEnveloping` sends a canonical generator `x` to
`ι_z(pr_z x) ⊗ 1 + 1 ⊗ ι_der(pr_der x)`. -/
theorem reductiveEnveloping_ι (x : L) :
    reductiveEnveloping K L (_root_.UniversalEnvelopingAlgebra.ι K x) =
      SymmetricAlgebra.ι K (center K L) (centerDerivedEquiv K L x).1 ⊗ₜ[K] (1 : UD) +
        (1 : SZ) ⊗ₜ[K] _root_.UniversalEnvelopingAlgebra.ι K (centerDerivedEquiv K L x).2 := by
  rw [reductiveEnveloping, AlgEquiv.trans_apply, mapEquiv_ι, productEnveloping_ι]

/-- On the inclusion of the centre, `reductiveEnveloping` is the inverse abelian comparison
tensored with one. -/
@[simp]
theorem reductiveEnveloping_map_incl_center
    (a : _root_.UniversalEnvelopingAlgebra K (center K L)) :
    reductiveEnveloping K L (map K (center K L).incl a) =
      (symmetricAlgebraEquiv K (center K L)).symm a ⊗ₜ[K] (1 : UD) := by
  rw [reductiveEnveloping, AlgEquiv.trans_apply, mapEquiv_map,
    centerDerivedEquiv_comp_incl_center, productEnveloping_map_inl]

/-- On the inclusion of the derived ideal, `reductiveEnveloping` is one tensored with the
element. -/
@[simp]
theorem reductiveEnveloping_map_incl_derivedSeries (u : UD) :
    reductiveEnveloping K L (map K (derivedSeries K L 1).incl u) = (1 : SZ) ⊗ₜ[K] u := by
  rw [reductiveEnveloping, AlgEquiv.trans_apply, mapEquiv_map,
    centerDerivedEquiv_comp_incl_derivedSeries, productEnveloping_map_inr]

/-- The inverse of `reductiveEnveloping` sends a pure tensor `a ⊗ u` to the product of the images
of `a` and `u` under the inclusions of the centre and of the derived ideal. -/
@[simp]
theorem reductiveEnveloping_symm_tmul (a : SZ) (u : UD) :
    (reductiveEnveloping K L).symm (a ⊗ₜ[K] u) =
      map K (center K L).incl (symmetricAlgebraEquiv K (center K L) a) *
        map K (derivedSeries K L 1).incl u := by
  apply (reductiveEnveloping K L).injective
  rw [AlgEquiv.apply_symm_apply, map_mul, reductiveEnveloping_map_incl_center,
    reductiveEnveloping_map_incl_derivedSeries, AlgEquiv.symm_apply_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

end Enveloping

section Naturality

variable {K : Type u} {L : Type v} {L' : Type w} [Field K] [CharZero K] [LieRing L]
  [LieAlgebra K L] [FiniteDimensional K L] [HasCentralRadical K L] [LieRing L']
  [LieAlgebra K L'] [FiniteDimensional K L'] [HasCentralRadical K L']

-- `hom_ext` uses the commutator Lie ring of the target algebra; `Sym(z(L')) ⊗ U([L', L'])` also
-- carries the scalar-extension Lie ring, which is not definitionally the same.
attribute [local instance 1100] LieRing.ofAssociativeRing

/-- `reductiveEnveloping` is natural for Lie maps sending the centre into the centre: such a map
acts on `Sym(z(L))` through its restriction to the centres and on `U([L, L])` through its
restriction to the derived ideals. -/
theorem reductiveEnveloping_naturality (f : L →ₗ⁅K⁆ L')
    (hf : ∀ z ∈ center K L, f z ∈ center K L') :
    (Algebra.TensorProduct.map
        (SymmetricAlgebra.map K ((centerRestrict f hf : center K L →ₗ[K] center K L')))
        (map K (derivedSeriesRestrict f))).comp (reductiveEnveloping K L).toAlgHom =
      (reductiveEnveloping K L').toAlgHom.comp (map K f) := by
  refine _root_.UniversalEnvelopingAlgebra.hom_ext K (LieHom.ext fun x => ?_)
  simp only [LieHom.comp_apply, AlgHom.coe_toLieHom, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
  rw [reductiveEnveloping_ι, map_ι, reductiveEnveloping_ι, centerDerivedEquiv_map f hf, map_add,
    Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
  simp only [SymmetricAlgebra.map_apply_ι, map_one, map_ι, LieHom.coe_toLinearMap]

end Naturality

section Center

variable (K : Type u) (L : Type v) [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [HasCentralRadical K L]

local notation "UL" => _root_.UniversalEnvelopingAlgebra K L
local notation "UD" => _root_.UniversalEnvelopingAlgebra K (derivedSeries K L 1)
local notation "SZ" => SymmetricAlgebra K (center K L)
local notation "ZD" => Subalgebra.center K UD

/-- The center of the enveloping algebra of a reductive Lie algebra:
`Z(U(L)) ≃ Sym(z(L)) ⊗ Z(U([L, L]))`, the restriction of `reductiveEnveloping` to the centers.
See `reductiveCenterEquiv_inclusion` for the inclusion square. -/
noncomputable def reductiveCenterEquiv : Subalgebra.center K UL ≃ₐ[K] SZ ⊗[K] ZD :=
  ((AlgEquiv.subalgebraMap (mapEquiv K (centerDerivedEquiv K L)) (Subalgebra.center K UL)).trans
    (Subalgebra.equivOfEq _ _ (Subalgebra.map_center_eq _))).trans
    (productCenterEquiv K (center K L) (derivedSeries K L 1))

/-- The inclusion square of `reductiveCenterEquiv`: followed by `id ⊗ val`, it is
`reductiveEnveloping` on the underlying central element. -/
@[simp]
theorem reductiveCenterEquiv_inclusion (z : Subalgebra.center K UL) :
    Algebra.TensorProduct.map (AlgHom.id K SZ) (ZD).val (reductiveCenterEquiv K L z) =
      reductiveEnveloping K L (z : UL) := by
  rw [reductiveCenterEquiv, AlgEquiv.trans_apply, productCenterEquiv_inclusion]
  rfl

/-- The inverse of `reductiveCenterEquiv` on a pure tensor `a ⊗ c` with `c` central is the product
of the images of `a` and `c` under the inclusions of the centre and of the derived ideal. -/
@[simp]
theorem reductiveCenterEquiv_symm_tmul (a : SZ) (c : ZD) :
    ((reductiveCenterEquiv K L).symm (a ⊗ₜ[K] c) : UL) =
      map K (center K L).incl (symmetricAlgebraEquiv K (center K L) a) *
        map K (derivedSeries K L 1).incl (c : UD) := by
  rw [← reductiveEnveloping_symm_tmul, AlgEquiv.eq_symm_apply, ← reductiveCenterEquiv_inclusion,
    AlgEquiv.apply_symm_apply, Algebra.TensorProduct.map_tmul]
  rfl

/-- **The center of the enveloping algebra of a reductive Lie algebra.** There is an algebra
equivalence `Z(U(L)) ≃ Sym(z(L)) ⊗ Z(U([L, L]))` which, followed by `id ⊗ val`, is
`reductiveEnveloping` on the underlying central element. -/
theorem exists_reductiveCenterEquiv :
    ∃ e : Subalgebra.center K UL ≃ₐ[K] SZ ⊗[K] ZD,
      ∀ z, Algebra.TensorProduct.map (AlgHom.id K SZ) (ZD).val (e z) =
        reductiveEnveloping K L (z : UL) :=
  ⟨reductiveCenterEquiv K L, reductiveCenterEquiv_inclusion K L⟩

end Center

end UniversalEnvelopingAlgebra

end TauCeti
