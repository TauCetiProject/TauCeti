/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Prod
public import TauCeti.Algebra.Lie.UniversalEnveloping.Product.Center

/-!
# The enveloping algebra of a Lie algebra with complementary ideals

Let `I` and `J` be complementary ideals of a Lie algebra `L` over a commutative ring `R`, with `I`
abelian. Addition `I × J → L` is an equivalence of Lie algebras (`LieIdeal.prodEquivOfIsCompl`),
and transporting the product comparison `TauCeti.UniversalEnvelopingAlgebra.productEnveloping`
through it gives the algebra equivalence

`U(L) ≃ Sym(I) ⊗ U(J)`  (`TauCeti.UniversalEnvelopingAlgebra.envelopingEquivOfIsCompl`),

which sends a canonical generator `x = i + j` to `ι_I(i) ⊗ 1 + 1 ⊗ ι_J(j)`, and whose inverse
multiplies the images of the two factor inclusions. For `I` free, its restriction to the centers
is the algebra equivalence

`Z(U(L)) ≃ Sym(I) ⊗ Z(U(J))`  (`TauCeti.UniversalEnvelopingAlgebra.centerEquivOfIsCompl`).

## Main definitions

* `TauCeti.UniversalEnvelopingAlgebra.envelopingEquivOfIsCompl`: `U(L) ≃ₐ[R] Sym(I) ⊗ U(J)` for
  complementary ideals `I` and `J` with `I` abelian.
* `TauCeti.UniversalEnvelopingAlgebra.centerEquivOfIsCompl`: `Z(U(L)) ≃ₐ[R] Sym(I) ⊗ Z(U(J))`,
  for `I` moreover free.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.envelopingEquivOfIsCompl_ι`: the value on a generator.
* `UniversalEnvelopingAlgebra.envelopingEquivOfIsCompl_map_incl_left` and
  `UniversalEnvelopingAlgebra.envelopingEquivOfIsCompl_map_incl_right`: the values on the
  enveloping algebras of the two ideals.
* `UniversalEnvelopingAlgebra.envelopingEquivOfIsCompl_symm_tmul`: the inverse on a pure tensor.
* `TauCeti.UniversalEnvelopingAlgebra.envelopingEquivOfIsCompl_naturality`: naturality for Lie
  maps preserving the two ideals.
* `TauCeti.UniversalEnvelopingAlgebra.centerEquivOfIsCompl_inclusion`: the inclusion square.
* `TauCeti.UniversalEnvelopingAlgebra.centerEquivOfIsCompl_symm_tmul`: the pure-tensor formula.

## References

* J. Dixmier, *Enveloping Algebras*, §1.6.
-/

public section

open scoped TensorProduct

universe u v w

namespace TauCeti.UniversalEnvelopingAlgebra

open _root_.UniversalEnvelopingAlgebra

section IsCompl

variable (R : Type u) {L : Type v} [CommRing R] [LieRing L] [LieAlgebra R L]
  (I J : LieIdeal R L) (h : IsCompl I J) [IsLieAbelian I]

local notation "UL" => _root_.UniversalEnvelopingAlgebra R L
local notation "UJ" => _root_.UniversalEnvelopingAlgebra R J
local notation "SI" => SymmetricAlgebra R I

/-- The enveloping algebra of a Lie algebra with complementary ideals `I` and `J`, `I` abelian:
`U(L) ≃ Sym(I) ⊗ U(J)`, the map induced by the inverse of addition `I × J ≃ L` followed by
`productEnveloping`. -/
noncomputable def envelopingEquivOfIsCompl : UL ≃ₐ[R] SI ⊗[R] UJ :=
  (mapEquiv R (LieIdeal.prodEquivOfIsCompl I J h).symm).trans (productEnveloping R I J)

/-- The definition of `envelopingEquivOfIsCompl`, for use outside this module. -/
theorem envelopingEquivOfIsCompl_def :
    envelopingEquivOfIsCompl R I J h =
      (mapEquiv R (LieIdeal.prodEquivOfIsCompl I J h).symm).trans (productEnveloping R I J) :=
  (rfl)

/-- `envelopingEquivOfIsCompl` sends a canonical generator `x = i + j` to
`ι_I(i) ⊗ 1 + 1 ⊗ ι_J(j)`. -/
theorem envelopingEquivOfIsCompl_ι (x : L) :
    envelopingEquivOfIsCompl R I J h (_root_.UniversalEnvelopingAlgebra.ι R x) =
      SymmetricAlgebra.ι R I ((LieIdeal.prodEquivOfIsCompl I J h).symm x).1 ⊗ₜ[R] (1 : UJ) +
        (1 : SI) ⊗ₜ[R]
          _root_.UniversalEnvelopingAlgebra.ι R ((LieIdeal.prodEquivOfIsCompl I J h).symm x).2 := by
  rw [envelopingEquivOfIsCompl, AlgEquiv.trans_apply, mapEquiv_ι, productEnveloping_ι]

/-- The `simp`-normal form of `envelopingEquivOfIsCompl_ι`, stated for the canonical generators as
`simp` writes them: `ι R x` unfolds to `mkAlgHom R L (TensorAlgebra.ι R x)`. -/
@[simp]
theorem envelopingEquivOfIsCompl_ι' (x : L) :
    envelopingEquivOfIsCompl R I J h
        (_root_.UniversalEnvelopingAlgebra.mkAlgHom R L (TensorAlgebra.ι R x)) =
      SymmetricAlgebra.ι R I ((LieIdeal.prodEquivOfIsCompl I J h).symm x).1 ⊗ₜ[R] (1 : UJ) +
        (1 : SI) ⊗ₜ[R] _root_.UniversalEnvelopingAlgebra.mkAlgHom R J
          (TensorAlgebra.ι R ((LieIdeal.prodEquivOfIsCompl I J h).symm x).2) := by
  simpa only [_root_.UniversalEnvelopingAlgebra.ι_apply] using
    envelopingEquivOfIsCompl_ι R I J h x

/-- The algebra homomorphism underlying `envelopingEquivOfIsCompl`: the map induced by the inverse
of addition `I × J ≃ L`, followed by `productEnveloping`. -/
theorem envelopingEquivOfIsCompl_toAlgHom :
    (envelopingEquivOfIsCompl R I J h).toAlgHom = (productEnveloping R I J).toAlgHom.comp
      (map R (LieIdeal.prodEquivOfIsCompl I J h).symm.toLieHom) :=
  AlgHom.ext fun x ↦ by
    rw [← mapEquiv_toAlgHom, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, AlgEquiv.toAlgHom_apply,
      AlgEquiv.toAlgHom_apply, envelopingEquivOfIsCompl, AlgEquiv.trans_apply]

/-- On the image of the map induced by a Lie homomorphism `g` into `L`,
`envelopingEquivOfIsCompl` is `productEnveloping` on the image of the map induced by `g` followed
by the inverse of addition. -/
private theorem _root_.UniversalEnvelopingAlgebra.envelopingEquivOfIsCompl_map {M : Type*}
    [LieRing M] [LieAlgebra R M] (g : M →ₗ⁅R⁆ L) (a : _root_.UniversalEnvelopingAlgebra R M) :
    envelopingEquivOfIsCompl R I J h (map R g a) = productEnveloping R I J
      (map R ((LieIdeal.prodEquivOfIsCompl I J h).symm.toLieHom.comp g) a) := by
  rw [map_comp]
  exact AlgHom.congr_fun (envelopingEquivOfIsCompl_toAlgHom R I J h) (map R g a)

/-- On the inclusion of `I`, `envelopingEquivOfIsCompl` is the inverse abelian comparison
tensored with one. -/
@[simp]
theorem _root_.UniversalEnvelopingAlgebra.envelopingEquivOfIsCompl_map_incl_left
    (a : _root_.UniversalEnvelopingAlgebra R I) :
    envelopingEquivOfIsCompl R I J h (map R I.incl a) =
      (symmetricAlgebraEquiv R I).symm a ⊗ₜ[R] (1 : UJ) := by
  rw [envelopingEquivOfIsCompl_map, LieIdeal.prodEquivOfIsCompl_symm_comp_incl_left,
    productEnveloping_map_inl]

/-- On the inclusion of `J`, `envelopingEquivOfIsCompl` is one tensored with the element. -/
@[simp]
theorem _root_.UniversalEnvelopingAlgebra.envelopingEquivOfIsCompl_map_incl_right (u : UJ) :
    envelopingEquivOfIsCompl R I J h (map R J.incl u) = (1 : SI) ⊗ₜ[R] u := by
  rw [envelopingEquivOfIsCompl_map, LieIdeal.prodEquivOfIsCompl_symm_comp_incl_right,
    productEnveloping_map_inr]

/-- The inverse of `envelopingEquivOfIsCompl` sends a pure tensor `a ⊗ u` to the product of the
images of `a` and `u` under the inclusions of `I` and of `J`. -/
@[simp]
theorem _root_.UniversalEnvelopingAlgebra.envelopingEquivOfIsCompl_symm_tmul (a : SI) (u : UJ) :
    (envelopingEquivOfIsCompl R I J h).symm (a ⊗ₜ[R] u) =
      map R I.incl (symmetricAlgebraEquiv R I a) * map R J.incl u := by
  apply (envelopingEquivOfIsCompl R I J h).injective
  simp [Algebra.TensorProduct.tmul_mul_tmul]

end IsCompl

section IsComplNaturality

variable {R : Type u} {L : Type v} {L' : Type w} [CommRing R] [LieRing L] [LieAlgebra R L]
  [LieRing L'] [LieAlgebra R L'] {I J : LieIdeal R L} (h : IsCompl I J) [IsLieAbelian I]
  {I' J' : LieIdeal R L'} (h' : IsCompl I' J') [IsLieAbelian I']

/-- `envelopingEquivOfIsCompl` is natural for Lie maps `f` sending `I` into `I'` and `J` into `J'`:
such a map acts on `Sym(I)` and on `U(J)` through its restrictions to the ideals. -/
theorem envelopingEquivOfIsCompl_naturality (f : L →ₗ⁅R⁆ L') (hI : ∀ x ∈ I, f x ∈ I')
    (hJ : ∀ x ∈ J, f x ∈ J') :
    (Algebra.TensorProduct.map (SymmetricAlgebra.map R ((f.restrictIdeal hI : I →ₗ[R] I')))
        (map R (f.restrictIdeal hJ))).comp (envelopingEquivOfIsCompl R I J h).toAlgHom =
      (envelopingEquivOfIsCompl R I' J' h').toAlgHom.comp (map R f) := by
  have hσ : ((f.restrictIdeal hI).prodMap (f.restrictIdeal hJ)).comp
      (LieIdeal.prodEquivOfIsCompl I J h).symm.toLieHom =
        (LieIdeal.prodEquivOfIsCompl I' J' h').symm.toLieHom.comp f :=
    LieHom.ext fun x ↦ by
      rw [LieHom.comp_apply, LieHom.comp_apply, LieHom.prodMap_apply, LieEquiv.coe_toLieHom,
        LieEquiv.coe_toLieHom, LieIdeal.prodEquivOfIsCompl_symm_map I J h h' f hI hJ x]
  rw [envelopingEquivOfIsCompl_toAlgHom, envelopingEquivOfIsCompl_toAlgHom, ← AlgHom.comp_assoc,
    productEnveloping_naturality, AlgHom.comp_assoc, ← map_comp, hσ, map_comp, AlgHom.comp_assoc]

end IsComplNaturality

section IsComplCenter

variable (R : Type u) {L : Type v} [CommRing R] [LieRing L] [LieAlgebra R L]
  (I J : LieIdeal R L) (h : IsCompl I J) [IsLieAbelian I] [Module.Free R I]

local notation "UL" => _root_.UniversalEnvelopingAlgebra R L
local notation "UJ" => _root_.UniversalEnvelopingAlgebra R J
local notation "SI" => SymmetricAlgebra R I
local notation "ZJ" => Subalgebra.center R UJ

/-- The center of the enveloping algebra of a Lie algebra with complementary ideals `I` and `J`,
`I` abelian and free: `Z(U(L)) ≃ Sym(I) ⊗ Z(U(J))`, the restriction of `envelopingEquivOfIsCompl`
to the centers. See `centerEquivOfIsCompl_inclusion` for the inclusion square. -/
noncomputable def centerEquivOfIsCompl : Subalgebra.center R UL ≃ₐ[R] SI ⊗[R] ZJ :=
  (Subalgebra.centerCongr (mapEquiv R (LieIdeal.prodEquivOfIsCompl I J h).symm)).trans
    (productCenterEquiv R I J)

/-- The definition of `centerEquivOfIsCompl`, for use outside this module. -/
theorem centerEquivOfIsCompl_def :
    centerEquivOfIsCompl R I J h =
      (Subalgebra.centerCongr (mapEquiv R (LieIdeal.prodEquivOfIsCompl I J h).symm)).trans
        (productCenterEquiv R I J) :=
  (rfl)

/-- The inclusion square of `centerEquivOfIsCompl`: followed by `id ⊗ val`, it is
`envelopingEquivOfIsCompl` on the underlying central element. -/
@[simp]
theorem centerEquivOfIsCompl_inclusion (z : Subalgebra.center R UL) :
    Algebra.TensorProduct.map (AlgHom.id R SI) (ZJ).val (centerEquivOfIsCompl R I J h z) =
      envelopingEquivOfIsCompl R I J h (z : UL) := by
  rw [centerEquivOfIsCompl, AlgEquiv.trans_apply, productCenterEquiv_inclusion]
  rw [envelopingEquivOfIsCompl, AlgEquiv.trans_apply]
  exact congrArg _ (Subalgebra.centerCongr_apply_coe _ z)

/-- The inverse of `centerEquivOfIsCompl` on a pure tensor `a ⊗ c` with `c` central is the product
of the images of `a` and `c` under the inclusions of `I` and of `J`. -/
@[simp]
theorem centerEquivOfIsCompl_symm_tmul (a : SI) (c : ZJ) :
    ((centerEquivOfIsCompl R I J h).symm (a ⊗ₜ[R] c) : UL) =
      map R I.incl (symmetricAlgebraEquiv R I a) * map R J.incl (c : UJ) := by
  rw [← envelopingEquivOfIsCompl_symm_tmul R I J h, AlgEquiv.eq_symm_apply,
    ← centerEquivOfIsCompl_inclusion]
  simp

end IsComplCenter

end TauCeti.UniversalEnvelopingAlgebra
