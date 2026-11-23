/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Reductive.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Functoriality
public import TauCeti.Algebra.Lie.UniversalEnveloping.ProductCenter

/-!
# The enveloping algebra and its center for a reductive Lie algebra

Let `I` and `J` be complementary ideals of a Lie algebra `L` over a commutative ring `R`, with `I`
abelian. Addition `I × J → L` is an equivalence of Lie algebras (`LieIdeal.prodEquivOfIsCompl`),
and transporting the product comparison `TauCeti.UniversalEnvelopingAlgebra.productEnveloping`
through it gives the algebra equivalence

`U(L) ≃ Sym(I) ⊗ U(J)`  (`UniversalEnvelopingAlgebra.envelopingEquivOfIsCompl`),

which sends a canonical generator `x = i + j` to `ι_I(i) ⊗ 1 + 1 ⊗ ι_J(j)`, and whose inverse
multiplies the images of the two factor inclusions. For `I` free, its restriction to the centers
is the algebra equivalence

`Z(U(L)) ≃ Sym(I) ⊗ Z(U(J))`  (`UniversalEnvelopingAlgebra.centerEquivOfIsCompl`).

For a finite-dimensional reductive Lie algebra `L` over a field of characteristic zero, the centre
and the derived ideal are complementary (`TauCeti.isCompl_center_derivedSeries`), and these
specialize to

`U(L) ≃ Sym(z(L)) ⊗ U([L, L])`  (`UniversalEnvelopingAlgebra.reductiveEnveloping`),

`Z(U(L)) ≃ Sym(z(L)) ⊗ Z(U([L, L]))`  (`UniversalEnvelopingAlgebra.reductiveCenterEquiv`).

The latter, followed by `id ⊗ (Z(U([L, L])) ↪ U([L, L]))`, is `reductiveEnveloping` on the
underlying central element. Both are built from universal properties: no Harish-Chandra theorem is
used.

## Main definitions

* `UniversalEnvelopingAlgebra.envelopingEquivOfIsCompl`: `U(L) ≃ₐ[R] Sym(I) ⊗ U(J)` for
  complementary ideals `I` and `J` with `I` abelian.
* `UniversalEnvelopingAlgebra.centerEquivOfIsCompl`: `Z(U(L)) ≃ₐ[R] Sym(I) ⊗ Z(U(J))`, for `I`
  moreover free.
* `UniversalEnvelopingAlgebra.reductiveEnveloping`: `U(L) ≃ₐ[K] Sym(z(L)) ⊗ U([L, L])`.
* `UniversalEnvelopingAlgebra.reductiveCenterEquiv`:
  `Z(U(L)) ≃ₐ[K] Sym(z(L)) ⊗ Z(U([L, L]))`.

## Main results

* `UniversalEnvelopingAlgebra.envelopingEquivOfIsCompl_ι` and
  `UniversalEnvelopingAlgebra.reductiveEnveloping_ι`: the value on a generator.
* `UniversalEnvelopingAlgebra.envelopingEquivOfIsCompl_symm_tmul` and
  `UniversalEnvelopingAlgebra.reductiveEnveloping_symm_tmul`: the inverse on a pure tensor.
* `UniversalEnvelopingAlgebra.envelopingEquivOfIsCompl_naturality` and
  `UniversalEnvelopingAlgebra.reductiveEnveloping_naturality`: naturality for Lie maps
  preserving the two ideals, respectively sending the centre into the centre.
* `UniversalEnvelopingAlgebra.centerEquivOfIsCompl_inclusion` and
  `UniversalEnvelopingAlgebra.reductiveCenterEquiv_inclusion`: the inclusion square.
* `UniversalEnvelopingAlgebra.centerEquivOfIsCompl_symm_tmul` and
  `UniversalEnvelopingAlgebra.reductiveCenterEquiv_symm_tmul`: the pure-tensor formula.

## References

* J. Dixmier, *Enveloping Algebras*, §1.6.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §19.1.
-/

public section

open scoped TensorProduct

open LieAlgebra

universe u v w

namespace UniversalEnvelopingAlgebra

open TauCeti TauCeti.UniversalEnvelopingAlgebra

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

/-- On the inclusion of `I`, `envelopingEquivOfIsCompl` is the inverse abelian comparison
tensored with one. -/
@[simp]
theorem envelopingEquivOfIsCompl_map_incl_left (a : _root_.UniversalEnvelopingAlgebra R I) :
    envelopingEquivOfIsCompl R I J h (map R I.incl a) =
      (symmetricAlgebraEquiv R I).symm a ⊗ₜ[R] (1 : UJ) := by
  rw [envelopingEquivOfIsCompl, AlgEquiv.trans_apply,
    show mapEquiv R _ (map R I.incl a) = _ from
      AlgHom.congr_fun (mapEquiv_toAlgHom_comp_map R _ I.incl) a,
    LieIdeal.prodEquivOfIsCompl_symm_comp_incl_left, productEnveloping_map_inl]

/-- On the inclusion of `J`, `envelopingEquivOfIsCompl` is one tensored with the element. -/
@[simp]
theorem envelopingEquivOfIsCompl_map_incl_right (u : UJ) :
    envelopingEquivOfIsCompl R I J h (map R J.incl u) = (1 : SI) ⊗ₜ[R] u := by
  rw [envelopingEquivOfIsCompl, AlgEquiv.trans_apply,
    show mapEquiv R _ (map R J.incl u) = _ from
      AlgHom.congr_fun (mapEquiv_toAlgHom_comp_map R _ J.incl) u,
    LieIdeal.prodEquivOfIsCompl_symm_comp_incl_right, productEnveloping_map_inr]

/-- The inverse of `envelopingEquivOfIsCompl` sends a pure tensor `a ⊗ u` to the product of the
images of `a` and `u` under the inclusions of `I` and of `J`. -/
@[simp]
theorem envelopingEquivOfIsCompl_symm_tmul (a : SI) (u : UJ) :
    (envelopingEquivOfIsCompl R I J h).symm (a ⊗ₜ[R] u) =
      map R I.incl (symmetricAlgebraEquiv R I a) * map R J.incl u := by
  apply (envelopingEquivOfIsCompl R I J h).injective
  rw [AlgEquiv.apply_symm_apply, map_mul, envelopingEquivOfIsCompl_map_incl_left,
    envelopingEquivOfIsCompl_map_incl_right, AlgEquiv.symm_apply_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

end IsCompl

section IsComplNaturality

variable {R : Type u} {L : Type v} {L' : Type w} [CommRing R] [LieRing L] [LieAlgebra R L]
  [LieRing L'] [LieAlgebra R L'] {I J : LieIdeal R L} (h : IsCompl I J) [IsLieAbelian I]
  {I' J' : LieIdeal R L'} (h' : IsCompl I' J') [IsLieAbelian I']

-- `hom_ext` uses the commutator Lie ring of the target algebra; `Sym(I') ⊗ U(J')` also carries the
-- scalar-extension Lie ring, which is not definitionally the same.
attribute [local instance 1100] LieRing.ofAssociativeRing

/-- `envelopingEquivOfIsCompl` is natural for Lie maps `f` sending `I` into `I'` and `J` into `J'`:
such a map acts on `Sym(I)` and on `U(J)` through its restrictions to the ideals. -/
theorem envelopingEquivOfIsCompl_naturality (f : L →ₗ⁅R⁆ L') (hI : ∀ x ∈ I, f x ∈ I')
    (hJ : ∀ x ∈ J, f x ∈ J') :
    (Algebra.TensorProduct.map (SymmetricAlgebra.map R ((f.restrictIdeal hI : I →ₗ[R] I')))
        (map R (f.restrictIdeal hJ))).comp (envelopingEquivOfIsCompl R I J h).toAlgHom =
      (envelopingEquivOfIsCompl R I' J' h').toAlgHom.comp (map R f) := by
  refine _root_.UniversalEnvelopingAlgebra.hom_ext R (LieHom.ext fun x => ?_)
  simp only [LieHom.comp_apply, AlgHom.coe_toLieHom, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
  rw [envelopingEquivOfIsCompl_ι, map_ι, envelopingEquivOfIsCompl_ι,
    LieIdeal.prodEquivOfIsCompl_symm_map I J h h' f hI hJ, map_add,
    Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
  simp only [SymmetricAlgebra.map_apply_ι, map_one, map_ι, LieHom.coe_toLinearMap]

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
    ← centerEquivOfIsCompl_inclusion, AlgEquiv.apply_symm_apply, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply, Subalgebra.coe_val]

end IsComplCenter

section Enveloping

variable (K : Type u) (L : Type v) [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [HasCentralRadical K L]

local notation "UL" => _root_.UniversalEnvelopingAlgebra K L
local notation "UD" => _root_.UniversalEnvelopingAlgebra K (derivedSeries K L 1)
local notation "SZ" => SymmetricAlgebra K (center K L)

/-- The enveloping algebra of a reductive Lie algebra: `U(L) ≃ Sym(z(L)) ⊗ U([L, L])`,
`envelopingEquivOfIsCompl` for the central/derived splitting. -/
noncomputable def reductiveEnveloping : UL ≃ₐ[K] SZ ⊗[K] UD :=
  envelopingEquivOfIsCompl K (center K L) (derivedSeries K L 1) (isCompl_center_derivedSeries K L)

/-- The definition of `reductiveEnveloping`, for use outside this module. -/
theorem reductiveEnveloping_def :
    reductiveEnveloping K L =
      envelopingEquivOfIsCompl K (center K L) (derivedSeries K L 1)
        (isCompl_center_derivedSeries K L) :=
  (rfl)

/-- `reductiveEnveloping` sends a canonical generator `x` to
`ι_z(pr_z x) ⊗ 1 + 1 ⊗ ι_der(pr_der x)`. -/
theorem reductiveEnveloping_ι (x : L) :
    reductiveEnveloping K L (_root_.UniversalEnvelopingAlgebra.ι K x) =
      SymmetricAlgebra.ι K (center K L) (centerDerivedEquiv K L x).1 ⊗ₜ[K] (1 : UD) +
        (1 : SZ) ⊗ₜ[K] _root_.UniversalEnvelopingAlgebra.ι K (centerDerivedEquiv K L x).2 := by
  rw [reductiveEnveloping, envelopingEquivOfIsCompl_ι, centerDerivedEquiv_def]

/-- The `simp`-normal form of `reductiveEnveloping_ι`, stated for the canonical generators as
`simp` writes them: `ι K x` unfolds to `mkAlgHom K L (TensorAlgebra.ι K x)`. -/
@[simp]
theorem reductiveEnveloping_ι' (x : L) :
    reductiveEnveloping K L (_root_.UniversalEnvelopingAlgebra.mkAlgHom K L (TensorAlgebra.ι K x)) =
      SymmetricAlgebra.ι K (center K L) (centerDerivedEquiv K L x).1 ⊗ₜ[K] (1 : UD) +
        (1 : SZ) ⊗ₜ[K] _root_.UniversalEnvelopingAlgebra.mkAlgHom K (derivedSeries K L 1)
          (TensorAlgebra.ι K (centerDerivedEquiv K L x).2) := by
  simpa only [_root_.UniversalEnvelopingAlgebra.ι_apply] using reductiveEnveloping_ι K L x

/-- On the inclusion of the centre, `reductiveEnveloping` is the inverse abelian comparison
tensored with one. -/
@[simp]
theorem reductiveEnveloping_map_incl_center
    (a : _root_.UniversalEnvelopingAlgebra K (center K L)) :
    reductiveEnveloping K L (map K (center K L).incl a) =
      (symmetricAlgebraEquiv K (center K L)).symm a ⊗ₜ[K] (1 : UD) :=
  envelopingEquivOfIsCompl_map_incl_left _ _ _ _ a

/-- On the inclusion of the derived ideal, `reductiveEnveloping` is one tensored with the
element. -/
@[simp]
theorem reductiveEnveloping_map_incl_derivedSeries (u : UD) :
    reductiveEnveloping K L (map K (derivedSeries K L 1).incl u) = (1 : SZ) ⊗ₜ[K] u :=
  envelopingEquivOfIsCompl_map_incl_right _ _ _ _ u

/-- The inverse of `reductiveEnveloping` sends a pure tensor `a ⊗ u` to the product of the images
of `a` and `u` under the inclusions of the centre and of the derived ideal. -/
@[simp]
theorem reductiveEnveloping_symm_tmul (a : SZ) (u : UD) :
    (reductiveEnveloping K L).symm (a ⊗ₜ[K] u) =
      map K (center K L).incl (symmetricAlgebraEquiv K (center K L) a) *
        map K (derivedSeries K L 1).incl u :=
  envelopingEquivOfIsCompl_symm_tmul _ _ _ _ a u

end Enveloping

section Naturality

variable {K : Type u} {L : Type v} {L' : Type w} [Field K] [CharZero K] [LieRing L]
  [LieAlgebra K L] [FiniteDimensional K L] [HasCentralRadical K L] [LieRing L']
  [LieAlgebra K L'] [FiniteDimensional K L'] [HasCentralRadical K L']

/-- `reductiveEnveloping` is natural for Lie maps sending the centre into the centre: such a map
acts on `Sym(z(L))` through its restriction to the centres and on `U([L, L])` through its
restriction to the derived ideals. -/
theorem reductiveEnveloping_naturality (f : L →ₗ⁅K⁆ L')
    (hf : ∀ z ∈ center K L, f z ∈ center K L') :
    (Algebra.TensorProduct.map
        (SymmetricAlgebra.map K ((f.restrictIdeal hf : center K L →ₗ[K] center K L')))
        (map K (f.restrictIdeal fun _ hx ↦
          LieIdeal.derivedSeries_map_le (f := f) 1 (LieIdeal.mem_map hx)))).comp
        (reductiveEnveloping K L).toAlgHom =
      (reductiveEnveloping K L').toAlgHom.comp (map K f) :=
  envelopingEquivOfIsCompl_naturality _ _ f hf _

end Naturality

section Center

variable (K : Type u) (L : Type v) [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [HasCentralRadical K L]

local notation "UL" => _root_.UniversalEnvelopingAlgebra K L
local notation "UD" => _root_.UniversalEnvelopingAlgebra K (derivedSeries K L 1)
local notation "SZ" => SymmetricAlgebra K (center K L)
local notation "ZD" => Subalgebra.center K UD

/-- The center of the enveloping algebra of a reductive Lie algebra:
`Z(U(L)) ≃ Sym(z(L)) ⊗ Z(U([L, L]))`, `centerEquivOfIsCompl` for the central/derived splitting.
See `reductiveCenterEquiv_inclusion` for the inclusion square. -/
noncomputable def reductiveCenterEquiv : Subalgebra.center K UL ≃ₐ[K] SZ ⊗[K] ZD :=
  centerEquivOfIsCompl K (center K L) (derivedSeries K L 1) (isCompl_center_derivedSeries K L)

/-- The inclusion square of `reductiveCenterEquiv`: followed by `id ⊗ val`, it is
`reductiveEnveloping` on the underlying central element. -/
@[simp]
theorem reductiveCenterEquiv_inclusion (z : Subalgebra.center K UL) :
    Algebra.TensorProduct.map (AlgHom.id K SZ) (ZD).val (reductiveCenterEquiv K L z) =
      reductiveEnveloping K L (z : UL) :=
  centerEquivOfIsCompl_inclusion _ _ _ _ z

/-- The inverse of `reductiveCenterEquiv` on a pure tensor `a ⊗ c` with `c` central is the product
of the images of `a` and `c` under the inclusions of the centre and of the derived ideal. -/
@[simp]
theorem reductiveCenterEquiv_symm_tmul (a : SZ) (c : ZD) :
    ((reductiveCenterEquiv K L).symm (a ⊗ₜ[K] c) : UL) =
      map K (center K L).incl (symmetricAlgebraEquiv K (center K L) a) *
        map K (derivedSeries K L 1).incl (c : UD) :=
  centerEquivOfIsCompl_symm_tmul _ _ _ _ a c

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
