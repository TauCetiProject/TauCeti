/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.Algebra.Lie.Ideal
public import Mathlib.Algebra.Lie.Subalgebra
public import TauCeti.Algebra.Lie.Restricted.Jacobson
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import TauCeti.Algebra.Lie.AdjointAction.Frobenius

/-!
# Restricted Lie algebras

A *restricted Lie algebra* (or *`p`-Lie algebra*, Jacobson 1941) over a commutative ring `R` is a
Lie algebra `L` over `R` equipped with a `p`-map `pMap : L → L` (`x ↦ x^[p]`) satisfying:

1. `p`-homogeneity: `pMap (c • x) = c ^ p • pMap x` for `c : R`, `x : L`;
2. adjoint compatibility: `LieAlgebra.ad R L (pMap x) = LieAlgebra.ad R L x ^ p`;
3. Jacobson's additivity law:
   `pMap (x + y) = pMap x + pMap y + FreeLieAlgebra.lift R ![x, y] (jacobsonLie R p)`.

The `p`-map is genuine data rather than a property: on an abelian Lie algebra `R` of prime
characteristic `p` with `1 ≠ 0`, `pMap = 0` (`ofAbelianZero`) and `pMap x = x ^ p`
(`ofAssociative`) are two distinct restricted structures on the same Lie algebra.

We develop the basic structural theory: morphisms of restricted Lie algebras (`RestrictedLieHom`)
with identity and composition, restricted Lie subalgebras (`RestrictedLieSubalgebra`) with induced
restricted structure, lattice bounds, and images (`RestrictedLieHom.range`), and restricted Lie
ideals (`RestrictedLieIdeal`) including kernels (`RestrictedLieHom.ker`). We construct the standard
examples: associative algebras of prime characteristic `p` (`ofAssociative`), endomorphism algebras
`Module.End R M` when `p` annihilates `M` pointwise (`ofModuleEnd`, including trivial
modules `M`), abelian Lie algebras with the zero `p`-map (`ofAbelianZero`), and the adjoint
morphisms `RestrictedLieHom.ad` and `RestrictedLieHom.adOfAssociative`.

## Main definitions

* `TauCeti.RestrictedLieAlgebra`: typeclass for a restricted Lie algebra structure on `L` over `R`.
* `TauCeti.RestrictedLieHom`: morphisms of restricted Lie algebras.
* `TauCeti.RestrictedLieSubalgebra`: Lie subalgebras closed under `pMap`.
* `TauCeti.RestrictedLieIdeal`: Lie ideals closed under `pMap`.
* `TauCeti.RestrictedLieAlgebra.ofAssociative`: the restricted Lie algebra structure `a ↦ a ^ p`
  on an associative algebra of prime characteristic `p`.
* `TauCeti.RestrictedLieAlgebra.ofModuleEnd`: the restricted Lie algebra structure `f ↦ f ^ p` on
  `Module.End R M` when `p` annihilates `M` pointwise.
* `TauCeti.RestrictedLieAlgebra.ofAbelianZero`: the zero `p`-map on an abelian Lie algebra
  (`p ≠ 0`).
* `TauCeti.RestrictedLieHom.ad`: `LieAlgebra.ad R L` as a restricted morphism for any restricted
  Lie algebra annihilated pointwise by `p`.
* `TauCeti.RestrictedLieHom.adOfAssociative`: `LieAlgebra.ad R A` as a restricted morphism for an
  associative algebra of characteristic `p`.

## References

* N. Jacobson, *Restricted Lie algebras of characteristic `p`*, Trans. Amer. Math. Soc. **50**
  (1941), 15–25.
* N. Jacobson, *Lie Algebras*, Interscience (1962), Chapter V, §7.
* N. M. Katz, *Nilpotent connections and the monodromy theorem: Applications of a result of
  Turrittin*, Publ. Math. IHÉS **39** (1970), §5.
-/

public section

namespace TauCeti

/-- A restricted Lie algebra (or `p`-Lie algebra, Jacobson 1941) over a commutative ring `R`: a Lie
algebra `L` equipped with a `p`-map `pMap : L → L` that is `p`-homogeneous, compatible with the
adjoint action, and satisfies Jacobson's additivity formula with `jacobsonLie R p`. -/
@[ext]
class RestrictedLieAlgebra (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] (p : ℕ) where
  /-- The `p`-map `x ↦ x^[p]`. -/
  pMap : L → L
  /-- `p`-homogeneity: `pMap (c • x) = c ^ p • pMap x`. -/
  pMap_smul (c : R) (x : L) : pMap (c • x) = c ^ p • pMap x
  /-- Compatibility with the adjoint action: `ad (pMap x) = (ad x) ^ p`. -/
  ad_pMap (x : L) : LieAlgebra.ad R L (pMap x) = LieAlgebra.ad R L x ^ p
  /-- Jacobson's additivity formula for `pMap (x + y)`. -/
  pMap_add (x y : L) :
    pMap (x + y) = pMap x + pMap y + FreeLieAlgebra.lift R ![x, y] (jacobsonLie R p)

namespace RestrictedLieAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] {p : ℕ}
  [RestrictedLieAlgebra R L p]

/-- Evaluating `ad_pMap` on an element `y : L`: `⁅pMap x, y⁆ = (ad R L x ^ p) y`. -/
theorem lie_pMap (x y : L) :
    ⁅pMap (R := R) (p := p) x, y⁆ = (LieAlgebra.ad R L x ^ p) y := by
  have h := congrArg (fun f : Module.End R L => f y) (ad_pMap (R := R) (p := p) x)
  simpa only [LieAlgebra.ad_apply] using h

/-- `pMap 0 = 0` for every `p : ℕ` (including `p = 0`). -/
@[simp]
theorem pMap_zero : pMap (R := R) (p := p) (0 : L) = 0 := by
  have h := pMap_add (R := R) (p := p) (0 : L) (0 : L)
  rw [add_zero, lift_jacobsonLie_zero_left, add_zero] at h
  exact add_left_cancel (by rw [add_zero]; exact h.symm)

/-- `pMap (-x) = (-1 : R) ^ p • pMap x`. -/
theorem pMap_neg (x : L) :
    pMap (R := R) (p := p) (-x) = (-1 : R) ^ p • pMap (R := R) (p := p) x := by
  rw [← neg_one_smul R x, pMap_smul]

/-- For odd `p`, `pMap (-x) = -pMap x`. -/
theorem pMap_neg_of_odd (hp : Odd p) (x : L) :
    pMap (R := R) (p := p) (-x) = -pMap (R := R) (p := p) x := by
  rw [pMap_neg, hp.neg_one_pow, neg_one_smul]

/-- For even `p`, `pMap (-x) = pMap x`. -/
theorem pMap_neg_of_even (hp : Even p) (x : L) :
    pMap (R := R) (p := p) (-x) = pMap (R := R) (p := p) x := by
  rw [pMap_neg, hp.neg_one_pow, one_smul]

/-- On commuting elements `x, y` (with `p ≠ 0`), `pMap` is additive. -/
theorem pMap_add_of_lie_eq_zero (hp : p ≠ 0) {x y : L} (h : ⁅x, y⁆ = 0) :
    pMap (R := R) (p := p) (x + y) = pMap (R := R) (p := p) x + pMap (R := R) (p := p) y := by
  rw [pMap_add, lift_jacobsonLie_eq_zero_of_lie_eq_zero hp h, add_zero]

/-- On commuting elements `x, y` (with `p ≠ 0`),
`pMap (x - y) = pMap x + (-1 : R) ^ p • pMap y`. -/
theorem pMap_sub_of_lie_eq_zero (hp : p ≠ 0) {x y : L} (h : ⁅x, y⁆ = 0) :
    pMap (R := R) (p := p) (x - y) =
      pMap (R := R) (p := p) x + (-1 : R) ^ p • pMap (R := R) (p := p) y := by
  rw [sub_eq_add_neg, pMap_add_of_lie_eq_zero hp (by rw [lie_neg, h, neg_zero]), pMap_neg]

/-- In an abelian restricted Lie algebra (`p ≠ 0`), `pMap` is additive. -/
theorem pMap_add_of_isLieAbelian [IsLieAbelian L] (hp : p ≠ 0) (x y : L) :
    pMap (R := R) (p := p) (x + y) = pMap (R := R) (p := p) x + pMap (R := R) (p := p) y :=
  pMap_add_of_lie_eq_zero hp (trivial_lie_zero L L x y)

/-- In an abelian restricted Lie algebra (`p ≠ 0`), `pMap` commutes with finite sums. -/
theorem pMap_sum_of_isLieAbelian [IsLieAbelian L] (hp : p ≠ 0) {ι : Type*} (s : Finset ι)
    (f : ι → L) :
    pMap (R := R) (p := p) (∑ i ∈ s, f i) = ∑ i ∈ s, pMap (R := R) (p := p) (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, pMap_add_of_isLieAbelian hp, ih, Finset.sum_insert ha]

end RestrictedLieAlgebra

section Hom

/-- A morphism of restricted Lie algebras over `R`: a Lie algebra morphism commuting with `pMap`. -/
structure RestrictedLieHom (R : Type*) (p : ℕ) (L L' : Type*) [CommRing R] [LieRing L]
    [LieAlgebra R L] [RestrictedLieAlgebra R L p] [LieRing L'] [LieAlgebra R L']
    [RestrictedLieAlgebra R L' p] extends L →ₗ⁅R⁆ L' where
  /-- A restricted Lie algebra morphism commutes with `pMap`. -/
  map_pMap' (x : L) :
    toFun (RestrictedLieAlgebra.pMap (R := R) (p := p) x) =
      RestrictedLieAlgebra.pMap (R := R) (p := p) (toFun x)

namespace RestrictedLieHom

variable {R : Type*} {p : ℕ} {L L' L'' L''' : Type*} [CommRing R]
  [LieRing L] [LieAlgebra R L] [RestrictedLieAlgebra R L p]
  [LieRing L'] [LieAlgebra R L'] [RestrictedLieAlgebra R L' p]
  [LieRing L''] [LieAlgebra R L''] [RestrictedLieAlgebra R L'' p]
  [LieRing L'''] [LieAlgebra R L'''] [RestrictedLieAlgebra R L''' p]

instance : FunLike (RestrictedLieHom R p L L') L L' where
  coe f := f.toLieHom
  coe_injective f g h := by
    cases f
    cases g
    congr
    exact DFunLike.coe_injective h

/-- Two restricted Lie algebra morphisms with the same underlying Lie algebra morphism are equal. -/
theorem toLieHom_injective :
    Function.Injective (toLieHom : RestrictedLieHom R p L L' → L →ₗ⁅R⁆ L') := by
  intro f g h
  cases f
  cases g
  cases h
  rfl

@[ext]
theorem ext {f g : RestrictedLieHom R p L L'} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[simp]
theorem coe_toLieHom (f : RestrictedLieHom R p L L') : ⇑f.toLieHom = f :=
  (rfl)

@[simp]
theorem toLieHom_apply (f : RestrictedLieHom R p L L') (x : L) : f.toLieHom x = f x :=
  (rfl)

@[simp]
theorem map_pMap (f : RestrictedLieHom R p L L') (x : L) :
    f (RestrictedLieAlgebra.pMap (R := R) (p := p) x) =
      RestrictedLieAlgebra.pMap (R := R) (p := p) (f x) :=
  f.map_pMap' x

@[simp]
theorem map_zero (f : RestrictedLieHom R p L L') : f 0 = 0 :=
  f.toLieHom.map_zero

@[simp]
theorem map_add (f : RestrictedLieHom R p L L') (x y : L) : f (x + y) = f x + f y :=
  f.toLieHom.map_add x y

@[simp]
theorem map_neg (f : RestrictedLieHom R p L L') (x : L) : f (-x) = -f x :=
  f.toLieHom.map_neg x

@[simp]
theorem map_sub (f : RestrictedLieHom R p L L') (x y : L) : f (x - y) = f x - f y :=
  f.toLieHom.map_sub x y

@[simp]
theorem map_smul (f : RestrictedLieHom R p L L') (c : R) (x : L) : f (c • x) = c • f x :=
  f.toLieHom.map_smul c x

@[simp]
theorem map_lie (f : RestrictedLieHom R p L L') (x y : L) : f ⁅x, y⁆ = ⁅f x, f y⁆ :=
  f.toLieHom.map_lie x y

/-- The identity morphism of a restricted Lie algebra. -/
def id (R : Type*) (p : ℕ) (L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
    [RestrictedLieAlgebra R L p] : RestrictedLieHom R p L L where
  toLieHom := LieHom.id
  map_pMap' _ := rfl

@[simp]
theorem id_apply (x : L) : id R p L x = x :=
  (rfl)

@[simp]
theorem toLieHom_id : (id R p L).toLieHom = LieHom.id :=
  (rfl)

/-- Composition of morphisms of restricted Lie algebras. -/
def comp (g : RestrictedLieHom R p L' L'') (f : RestrictedLieHom R p L L') :
    RestrictedLieHom R p L L'' where
  toLieHom := g.toLieHom.comp f.toLieHom
  map_pMap' x := (congrArg g (f.map_pMap x)).trans (g.map_pMap (f x))

@[simp]
theorem comp_apply (g : RestrictedLieHom R p L' L'') (f : RestrictedLieHom R p L L') (x : L) :
    (g.comp f) x = g (f x) :=
  (rfl)

@[simp]
theorem toLieHom_comp (g : RestrictedLieHom R p L' L'') (f : RestrictedLieHom R p L L') :
    (g.comp f).toLieHom = g.toLieHom.comp f.toLieHom :=
  (rfl)

@[simp]
theorem id_comp (f : RestrictedLieHom R p L L') : (id R p L').comp f = f := by
  ext x
  rfl

@[simp]
theorem comp_id (f : RestrictedLieHom R p L L') : f.comp (id R p L) = f := by
  ext x
  rfl

theorem comp_assoc (h : RestrictedLieHom R p L'' L''') (g : RestrictedLieHom R p L' L'')
    (f : RestrictedLieHom R p L L') :
    (h.comp g).comp f = h.comp (g.comp f) := by
  ext x
  rfl

end RestrictedLieHom

end Hom

section Subalgebra

/-- A restricted Lie subalgebra of a restricted Lie algebra `L`: a Lie subalgebra closed under
the `p`-map `RestrictedLieAlgebra.pMap`. -/
structure RestrictedLieSubalgebra (R : Type*) (p : ℕ) (L : Type*) [CommRing R] [LieRing L]
    [LieAlgebra R L] [RestrictedLieAlgebra R L p] extends LieSubalgebra R L where
  /-- Closure under `pMap`. -/
  pMap_mem' {x : L} : x ∈ carrier → RestrictedLieAlgebra.pMap (R := R) (p := p) x ∈ carrier

namespace RestrictedLieSubalgebra

variable {R : Type*} {p : ℕ} {L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [RestrictedLieAlgebra R L p]

instance : SetLike (RestrictedLieSubalgebra R p L) L where
  coe S := S.carrier
  coe_injective S T h := by
    cases S
    cases T
    congr
    exact SetLike.coe_injective h

theorem toLieSubalgebra_injective :
    Function.Injective (toLieSubalgebra : RestrictedLieSubalgebra R p L → LieSubalgebra R L) := by
  intro S T h
  cases S
  cases T
  cases h
  rfl

@[ext]
theorem ext {S T : RestrictedLieSubalgebra R p L} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

@[simp]
theorem mem_toLieSubalgebra {S : RestrictedLieSubalgebra R p L} {x : L} :
    x ∈ S.toLieSubalgebra ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem coe_toLieSubalgebra (S : RestrictedLieSubalgebra R p L) :
    (S.toLieSubalgebra : Set L) = S :=
  (rfl)

theorem pMap_mem (S : RestrictedLieSubalgebra R p L) {x : L} (hx : x ∈ S) :
    RestrictedLieAlgebra.pMap (R := R) (p := p) x ∈ S :=
  S.pMap_mem' hx

theorem zero_mem (S : RestrictedLieSubalgebra R p L) : (0 : L) ∈ S :=
  S.toLieSubalgebra.zero_mem

theorem add_mem (S : RestrictedLieSubalgebra R p L) {x y : L} (hx : x ∈ S) (hy : y ∈ S) :
    x + y ∈ S :=
  S.toLieSubalgebra.add_mem hx hy

theorem neg_mem (S : RestrictedLieSubalgebra R p L) {x : L} (hx : x ∈ S) : -x ∈ S :=
  S.toLieSubalgebra.neg_mem hx

theorem sub_mem (S : RestrictedLieSubalgebra R p L) {x y : L} (hx : x ∈ S) (hy : y ∈ S) :
    x - y ∈ S :=
  S.toLieSubalgebra.sub_mem hx hy

theorem smul_mem (S : RestrictedLieSubalgebra R p L) (c : R) {x : L} (hx : x ∈ S) :
    c • x ∈ S :=
  S.toLieSubalgebra.smul_mem c hx

theorem lie_mem (S : RestrictedLieSubalgebra R p L) {x y : L} (hx : x ∈ S) (hy : y ∈ S) :
    ⁅x, y⁆ ∈ S :=
  S.toLieSubalgebra.lie_mem hx hy

instance instLieRing (S : RestrictedLieSubalgebra R p L) : LieRing S :=
  S.toLieSubalgebra.lieRing

instance instLieAlgebra (S : RestrictedLieSubalgebra R p L) : LieAlgebra R S :=
  S.toLieSubalgebra.lieAlgebra

@[simp]
theorem coe_zero (S : RestrictedLieSubalgebra R p L) : ((0 : S) : L) = 0 :=
  (rfl)

@[simp]
theorem coe_add (S : RestrictedLieSubalgebra R p L) (x y : S) : ((x + y : S) : L) = x + y :=
  (rfl)

@[simp]
theorem coe_neg (S : RestrictedLieSubalgebra R p L) (x : S) : ((-x : S) : L) = -x :=
  (rfl)

@[simp]
theorem coe_sub (S : RestrictedLieSubalgebra R p L) (x y : S) : ((x - y : S) : L) = x - y :=
  (rfl)

@[simp]
theorem coe_smul (S : RestrictedLieSubalgebra R p L) (c : R) (x : S) : ((c • x : S) : L) = c • x :=
  (rfl)

@[simp]
theorem coe_lie (S : RestrictedLieSubalgebra R p L) (x y : S) :
    ((⁅x, y⁆ : S) : L) = ⁅(x : L), (y : L)⁆ :=
  (rfl)

/-- The canonical Lie algebra inclusion `S →ₗ⁅R⁆ L`. -/
private def toLieHomIncl (S : RestrictedLieSubalgebra R p L) : S →ₗ⁅R⁆ L where
  toFun x := (x : L)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := rfl

/-- A restricted Lie subalgebra inherits a restricted Lie algebra structure from the ambient
restricted Lie algebra. -/
instance instRestrictedLieAlgebra (S : RestrictedLieSubalgebra R p L) :
    RestrictedLieAlgebra R S p where
  pMap x := ⟨RestrictedLieAlgebra.pMap (R := R) (p := p) (x : L), S.pMap_mem x.property⟩
  pMap_smul c x := by
    apply Subtype.ext
    exact RestrictedLieAlgebra.pMap_smul c (x : L)
  ad_pMap x := by
    refine LinearMap.ext fun y => Subtype.ext ?_
    have had : ∀ n : ℕ, ((LieAlgebra.ad R S x ^ n) y : L) = (LieAlgebra.ad R L x ^ n) y := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ', pow_succ', mul_apply_eq_comp, mul_apply_eq_comp, LieAlgebra.ad_apply,
          LieAlgebra.ad_apply, coe_lie, ih]
    rw [had p, LieAlgebra.ad_apply, coe_lie]
    exact RestrictedLieAlgebra.lie_pMap (R := R) (p := p) (x : L) (y : L)
  pMap_add x y := by
    refine Subtype.ext ?_
    have hincl : (FreeLieAlgebra.lift R ![x, y] (jacobsonLie R p) : L) =
        FreeLieAlgebra.lift R ![(x : L), (y : L)] (jacobsonLie R p) :=
      map_lift_jacobsonLie p S.toLieHomIncl x y
    dsimp only
    rw [coe_add, coe_add, coe_add, hincl]
    exact RestrictedLieAlgebra.pMap_add (R := R) (p := p) (x : L) (y : L)

@[simp]
theorem coe_pMap (S : RestrictedLieSubalgebra R p L) (x : S) :
    ((RestrictedLieAlgebra.pMap (R := R) (p := p) x : S) : L) =
      RestrictedLieAlgebra.pMap (R := R) (p := p) (x : L) :=
  (rfl)

/-- The canonical inclusion `S → L` of a restricted Lie subalgebra as a restricted morphism. -/
def incl (S : RestrictedLieSubalgebra R p L) : RestrictedLieHom R p S L where
  toLieHom := S.toLieHomIncl
  map_pMap' _ := rfl

@[simp]
theorem incl_apply (S : RestrictedLieSubalgebra R p L) (x : S) : S.incl x = x :=
  (rfl)

theorem incl_injective (S : RestrictedLieSubalgebra R p L) : Function.Injective S.incl :=
  Subtype.val_injective

instance : Top (RestrictedLieSubalgebra R p L) where
  top :=
    { toLieSubalgebra := ⊤
      pMap_mem' := fun _ => Set.mem_univ _ }

@[simp]
theorem mem_top (x : L) : x ∈ (⊤ : RestrictedLieSubalgebra R p L) :=
  Set.mem_univ x

instance : Bot (RestrictedLieSubalgebra R p L) where
  bot :=
    { toLieSubalgebra := ⊥
      pMap_mem' := fun hx => by
        have h0 : _ = (0 : L) := hx
        rw [h0]
        simp }

@[simp]
theorem mem_bot {x : L} : x ∈ (⊥ : RestrictedLieSubalgebra R p L) ↔ x = 0 :=
  Iff.rfl

instance : Min (RestrictedLieSubalgebra R p L) where
  min S T :=
    { toLieSubalgebra := S.toLieSubalgebra ⊓ T.toLieSubalgebra
      pMap_mem' := fun ⟨hxS, hxT⟩ => ⟨S.pMap_mem hxS, T.pMap_mem hxT⟩ }

@[simp]
theorem mem_inf {S T : RestrictedLieSubalgebra R p L} {x : L} :
    x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T :=
  Iff.rfl

end RestrictedLieSubalgebra

/-- The image of a restricted Lie algebra morphism, as a restricted Lie subalgebra. -/
def RestrictedLieHom.range {R : Type*} {p : ℕ} {L L' : Type*} [CommRing R] [LieRing L]
    [LieAlgebra R L] [RestrictedLieAlgebra R L p] [LieRing L'] [LieAlgebra R L']
    [RestrictedLieAlgebra R L' p] (f : RestrictedLieHom R p L L') :
    RestrictedLieSubalgebra R p L' where
  toLieSubalgebra := f.toLieHom.range
  pMap_mem' := by
    rintro y ⟨x, rfl⟩
    exact ⟨RestrictedLieAlgebra.pMap (R := R) (p := p) x, f.map_pMap x⟩

@[simp]
theorem RestrictedLieHom.mem_range {R : Type*} {p : ℕ} {L L' : Type*} [CommRing R] [LieRing L]
    [LieAlgebra R L] [RestrictedLieAlgebra R L p] [LieRing L'] [LieAlgebra R L']
    [RestrictedLieAlgebra R L' p] (f : RestrictedLieHom R p L L') {y : L'} :
    y ∈ f.range ↔ ∃ x : L, f x = y :=
  Iff.rfl

end Subalgebra

section Ideal

/-- A restricted Lie ideal of a restricted Lie algebra `L`: a Lie ideal closed under the `p`-map
`RestrictedLieAlgebra.pMap`. -/
structure RestrictedLieIdeal (R : Type*) (p : ℕ) (L : Type*) [CommRing R] [LieRing L]
    [LieAlgebra R L] [RestrictedLieAlgebra R L p] where
  /-- The underlying Lie ideal. -/
  toLieIdeal : LieIdeal R L
  /-- Closure under `pMap`. -/
  pMap_mem' {x : L} : x ∈ toLieIdeal → RestrictedLieAlgebra.pMap (R := R) (p := p) x ∈ toLieIdeal

namespace RestrictedLieIdeal

variable {R : Type*} {p : ℕ} {L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [RestrictedLieAlgebra R L p]

instance : SetLike (RestrictedLieIdeal R p L) L where
  coe I := (I.toLieIdeal : Set L)
  coe_injective I J h := by
    cases I
    cases J
    congr
    exact SetLike.coe_injective h

theorem toLieIdeal_injective :
    Function.Injective (toLieIdeal : RestrictedLieIdeal R p L → LieIdeal R L) := by
  intro I J h
  cases I
  cases J
  cases h
  rfl

@[ext]
theorem ext {I J : RestrictedLieIdeal R p L} (h : ∀ x, x ∈ I ↔ x ∈ J) : I = J :=
  SetLike.ext h

@[simp]
theorem mem_toLieIdeal {I : RestrictedLieIdeal R p L} {x : L} :
    x ∈ I.toLieIdeal ↔ x ∈ I :=
  Iff.rfl

@[simp]
theorem coe_toLieIdeal (I : RestrictedLieIdeal R p L) : (I.toLieIdeal : Set L) = I :=
  (rfl)

theorem pMap_mem (I : RestrictedLieIdeal R p L) {x : L} (hx : x ∈ I) :
    RestrictedLieAlgebra.pMap (R := R) (p := p) x ∈ I :=
  I.pMap_mem' hx

theorem zero_mem (I : RestrictedLieIdeal R p L) : (0 : L) ∈ I :=
  I.toLieIdeal.zero_mem

theorem add_mem (I : RestrictedLieIdeal R p L) {x y : L} (hx : x ∈ I) (hy : y ∈ I) :
    x + y ∈ I :=
  I.toLieIdeal.add_mem hx hy

theorem neg_mem (I : RestrictedLieIdeal R p L) {x : L} (hx : x ∈ I) : -x ∈ I :=
  I.toLieIdeal.neg_mem hx

theorem sub_mem (I : RestrictedLieIdeal R p L) {x y : L} (hx : x ∈ I) (hy : y ∈ I) :
    x - y ∈ I :=
  I.toLieIdeal.sub_mem hx hy

theorem smul_mem (I : RestrictedLieIdeal R p L) (c : R) {x : L} (hx : x ∈ I) : c • x ∈ I :=
  I.toLieIdeal.smul_mem c hx

theorem lie_mem_right (I : RestrictedLieIdeal R p L) (x : L) {y : L} (hy : y ∈ I) :
    ⁅x, y⁆ ∈ I :=
  _root_.lie_mem_right R L I.toLieIdeal x y hy

theorem lie_mem_left (I : RestrictedLieIdeal R p L) {x : L} (y : L) (hx : x ∈ I) :
    ⁅x, y⁆ ∈ I :=
  _root_.lie_mem_left R L I.toLieIdeal x y hx

/-- View a restricted Lie ideal as a restricted Lie subalgebra. -/
def toRestrictedLieSubalgebra (I : RestrictedLieIdeal R p L) :
    RestrictedLieSubalgebra R p L where
  toLieSubalgebra := I.toLieIdeal.toLieSubalgebra
  pMap_mem' := I.pMap_mem'

@[simp]
theorem mem_toRestrictedLieSubalgebra (I : RestrictedLieIdeal R p L) {x : L} :
    x ∈ I.toRestrictedLieSubalgebra ↔ x ∈ I :=
  Iff.rfl

instance instLieRing (I : RestrictedLieIdeal R p L) : LieRing I :=
  LieIdeal.lieRing R L I.toLieIdeal

instance instLieAlgebra (I : RestrictedLieIdeal R p L) : LieAlgebra R I :=
  LieIdeal.lieAlgebra R L I.toLieIdeal

@[simp]
theorem coe_zero (I : RestrictedLieIdeal R p L) : ((0 : I) : L) = 0 :=
  (rfl)

@[simp]
theorem coe_add (I : RestrictedLieIdeal R p L) (x y : I) : ((x + y : I) : L) = x + y :=
  (rfl)

@[simp]
theorem coe_neg (I : RestrictedLieIdeal R p L) (x : I) : ((-x : I) : L) = -x :=
  (rfl)

@[simp]
theorem coe_sub (I : RestrictedLieIdeal R p L) (x y : I) : ((x - y : I) : L) = x - y :=
  (rfl)

@[simp]
theorem coe_smul (I : RestrictedLieIdeal R p L) (c : R) (x : I) : ((c • x : I) : L) = c • x :=
  (rfl)

@[simp]
theorem coe_lie (I : RestrictedLieIdeal R p L) (x y : I) :
    ((⁅x, y⁆ : I) : L) = ⁅(x : L), (y : L)⁆ :=
  (rfl)

/-- The canonical Lie algebra inclusion `I →ₗ⁅R⁆ L`. -/
private def toLieHomIncl (I : RestrictedLieIdeal R p L) : I →ₗ⁅R⁆ L where
  toFun x := (x : L)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := rfl

instance instRestrictedLieAlgebra (I : RestrictedLieIdeal R p L) :
    RestrictedLieAlgebra R I p where
  pMap x := ⟨RestrictedLieAlgebra.pMap (R := R) (p := p) (x : L), I.pMap_mem x.property⟩
  pMap_smul c x := by
    apply Subtype.ext
    exact RestrictedLieAlgebra.pMap_smul c (x : L)
  ad_pMap x := by
    refine LinearMap.ext fun y => Subtype.ext ?_
    have had : ∀ n : ℕ, ((LieAlgebra.ad R I x ^ n) y : L) = (LieAlgebra.ad R L x ^ n) y := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ', pow_succ', mul_apply_eq_comp, mul_apply_eq_comp, LieAlgebra.ad_apply,
          LieAlgebra.ad_apply, coe_lie, ih]
    rw [had p, LieAlgebra.ad_apply, coe_lie]
    exact RestrictedLieAlgebra.lie_pMap (R := R) (p := p) (x : L) (y : L)
  pMap_add x y := by
    refine Subtype.ext ?_
    have hincl : (FreeLieAlgebra.lift R ![x, y] (jacobsonLie R p) : L) =
        FreeLieAlgebra.lift R ![(x : L), (y : L)] (jacobsonLie R p) :=
      map_lift_jacobsonLie p I.toLieHomIncl x y
    dsimp only
    rw [coe_add, coe_add, coe_add, hincl]
    exact RestrictedLieAlgebra.pMap_add (R := R) (p := p) (x : L) (y : L)

@[simp]
theorem coe_pMap (I : RestrictedLieIdeal R p L) (x : I) :
    ((RestrictedLieAlgebra.pMap (R := R) (p := p) x : I) : L) =
      RestrictedLieAlgebra.pMap (R := R) (p := p) (x : L) :=
  (rfl)

/-- The canonical inclusion `I → L` of a restricted Lie ideal as a restricted morphism. -/
def incl (I : RestrictedLieIdeal R p L) : RestrictedLieHom R p I L where
  toLieHom := I.toLieHomIncl
  map_pMap' _ := rfl

@[simp]
theorem incl_apply (I : RestrictedLieIdeal R p L) (x : I) : I.incl x = x :=
  (rfl)

theorem incl_injective (I : RestrictedLieIdeal R p L) : Function.Injective I.incl :=
  Subtype.val_injective

instance : Top (RestrictedLieIdeal R p L) where
  top :=
    { toLieIdeal := ⊤
      pMap_mem' := fun _ => trivial }

@[simp]
theorem mem_top (x : L) : x ∈ (⊤ : RestrictedLieIdeal R p L) :=
  trivial

instance : Bot (RestrictedLieIdeal R p L) where
  bot :=
    { toLieIdeal := ⊥
      pMap_mem' := fun hx => by
        rw [LieSubmodule.mem_bot] at hx ⊢
        rw [hx, RestrictedLieAlgebra.pMap_zero] }

@[simp]
theorem mem_bot {x : L} : x ∈ (⊥ : RestrictedLieIdeal R p L) ↔ x = 0 :=
  LieSubmodule.mem_bot x

instance : Min (RestrictedLieIdeal R p L) where
  min I J :=
    { toLieIdeal := I.toLieIdeal ⊓ J.toLieIdeal
      pMap_mem' := fun ⟨hxI, hxJ⟩ => ⟨I.pMap_mem hxI, J.pMap_mem hxJ⟩ }

@[simp]
theorem mem_inf {I J : RestrictedLieIdeal R p L} {x : L} :
    x ∈ I ⊓ J ↔ x ∈ I ∧ x ∈ J :=
  Iff.rfl

end RestrictedLieIdeal

/-- The kernel of a restricted Lie algebra morphism, as a restricted Lie ideal (valid for all
`p : ℕ` because `pMap 0 = 0`). -/
def RestrictedLieHom.ker {R : Type*} {p : ℕ} {L L' : Type*} [CommRing R] [LieRing L]
    [LieAlgebra R L] [RestrictedLieAlgebra R L p] [LieRing L'] [LieAlgebra R L']
    [RestrictedLieAlgebra R L' p] (f : RestrictedLieHom R p L L') :
    RestrictedLieIdeal R p L where
  toLieIdeal := f.toLieHom.ker
  pMap_mem' {x} hx := by
    rw [LieHom.mem_ker, RestrictedLieHom.toLieHom_apply] at hx ⊢
    rw [f.map_pMap, hx, RestrictedLieAlgebra.pMap_zero]

@[simp]
theorem RestrictedLieHom.mem_ker {R : Type*} {p : ℕ} {L L' : Type*} [CommRing R] [LieRing L]
    [LieAlgebra R L] [RestrictedLieAlgebra R L p] [LieRing L'] [LieAlgebra R L']
    [RestrictedLieAlgebra R L' p] (f : RestrictedLieHom R p L L') {x : L} :
    x ∈ f.ker ↔ f x = 0 :=
  LieHom.mem_ker (f := f.toLieHom)

end Ideal

section ExamplesDefs

/-- The trivial (zero) restricted Lie algebra structure on an abelian Lie algebra (`p ≠ 0`). -/
@[instance_reducible]
def RestrictedLieAlgebra.ofAbelianZero (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
    [IsLieAbelian L] (p : ℕ) (hp : p ≠ 0) : RestrictedLieAlgebra R L p where
  pMap _ := 0
  pMap_smul _ _ := (smul_zero _).symm
  ad_pMap x := by
    have h0 : LieAlgebra.ad R L x = 0 := by
      ext y
      exact trivial_lie_zero L L x y
    rw [map_zero, h0, zero_pow hp]
  pMap_add x y := by
    rw [add_zero, lift_jacobsonLie_eq_zero_of_lie_eq_zero hp (trivial_lie_zero L L x y), add_zero]

@[simp]
theorem RestrictedLieAlgebra.ofAbelianZero_pMap (R L : Type*) [CommRing R] [LieRing L]
    [LieAlgebra R L] [IsLieAbelian L] (p : ℕ) (hp : p ≠ 0) (x : L) :
    (ofAbelianZero R L p hp).pMap x = 0 :=
  (rfl)

section Associative

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The restricted Lie algebra structure `a ↦ a ^ p` on an associative `R`-algebra `A` of prime
characteristic `p`. Defined as a `def` rather than a global `instance` because
`LieRing.ofAssociativeRing` is a local instance. -/
@[instance_reducible]
def RestrictedLieAlgebra.ofAssociative (R A : Type*) [CommRing R] [Ring A] [Algebra R A]
    (p : ℕ) [Fact p.Prime] [CharP A p] : RestrictedLieAlgebra R A p where
  pMap a := a ^ p
  pMap_smul c a := smul_pow c a p
  ad_pMap a := by
    have : ExpChar A p := ExpChar.prime Fact.out
    simpa only [pow_one] using TauCeti.LieAlgebra.ad_pow_expChar_pow (R := R) p a 1
  pMap_add a b := add_pow_eq_jacobson R p a b

@[simp]
theorem RestrictedLieAlgebra.ofAssociative_pMap (R A : Type*) [CommRing R] [Ring A] [Algebra R A]
    (p : ℕ) [Fact p.Prime] [CharP A p] (a : A) :
    (ofAssociative R A p).pMap a = a ^ p :=
  (rfl)

private theorem charP_moduleEnd_of_nontrivial (R M : Type*) [CommRing R] [AddCommGroup M]
    [Module R M] [Nontrivial M] (p : ℕ) [Fact p.Prime] (hM : ∀ m : M, p • m = 0) :
    CharP (Module.End R M) p := by
  have : Nontrivial (Module.End R M) := by
    obtain ⟨m, hm⟩ := exists_ne (0 : M)
    exact ⟨1, 0, fun h => hm (by simpa using LinearMap.congr_fun h m)⟩
  have hp0 : (p : Module.End R M) = 0 := by
    ext m
    rw [natCast_apply_eq_smul, hM m, LinearMap.zero_apply]
  exact (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hp0

/-- The restricted Lie algebra structure `f ↦ f ^ p` on `Module.End R M` for prime `p`, whenever
`p` annihilates `M` pointwise (`∀ m : M, p • m = 0`). Valid for every such `R`-module `M`,
including trivial modules where `CharP (Module.End R M) p` does not hold and modules over
mixed-characteristic base rings `R`. -/
@[instance_reducible]
def RestrictedLieAlgebra.ofModuleEnd (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (p : ℕ) [Fact p.Prime] (hM : ∀ m : M, p • m = 0) :
    RestrictedLieAlgebra R (Module.End R M) p where
  pMap f := f ^ p
  pMap_smul c f := smul_pow c f p
  ad_pMap f := by
    rcases subsingleton_or_nontrivial M with hsub | hnt
    · exact Subsingleton.elim _ _
    · have : CharP (Module.End R M) p := charP_moduleEnd_of_nontrivial R M p hM
      exact (ofAssociative R (Module.End R M) p).ad_pMap f
  pMap_add f g := by
    rcases subsingleton_or_nontrivial M with hsub | hnt
    · exact Subsingleton.elim _ _
    · have : CharP (Module.End R M) p := charP_moduleEnd_of_nontrivial R M p hM
      exact (ofAssociative R (Module.End R M) p).pMap_add f g

@[simp]
theorem RestrictedLieAlgebra.ofModuleEnd_pMap (R M : Type*) [CommRing R] [AddCommGroup M]
    [Module R M] (p : ℕ) [Fact p.Prime] (hM : ∀ m : M, p • m = 0) (f : Module.End R M) :
    (ofModuleEnd R M p hM).pMap f = f ^ p :=
  (rfl)

/-- When `Module.End R M` has characteristic `p`, `ofModuleEnd` agrees with `ofAssociative`. -/
theorem RestrictedLieAlgebra.ofModuleEnd_eq_ofAssociative (R M : Type*) [CommRing R]
    [AddCommGroup M] [Module R M] (p : ℕ) [Fact p.Prime] (hM : ∀ m : M, p • m = 0)
    [CharP (Module.End R M) p] :
    ofModuleEnd R M p hM = ofAssociative R (Module.End R M) p :=
  RestrictedLieAlgebra.ext rfl

/-- The adjoint representation `LieAlgebra.ad R L : L →ₗ⁅R⁆ Module.End R L` of a restricted Lie
algebra annihilated pointwise by `p` (`∀ x : L, p • x = 0`), as a morphism of restricted Lie
algebras into `ofModuleEnd R L p hL`. -/
def RestrictedLieHom.ad (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] (p : ℕ)
    [Fact p.Prime] [RestrictedLieAlgebra R L p] (hL : ∀ x : L, p • x = 0) :
    @RestrictedLieHom R p L (Module.End R L) _ _ _ _ _ _
      (RestrictedLieAlgebra.ofModuleEnd R L p hL) :=
  @RestrictedLieHom.mk R p L (Module.End R L) _ _ _ _ _ _
    (RestrictedLieAlgebra.ofModuleEnd R L p hL) (LieAlgebra.ad R L)
    (fun x => RestrictedLieAlgebra.ad_pMap (R := R) (p := p) x)

@[simp]
theorem RestrictedLieHom.ad_apply (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] (p : ℕ)
    [Fact p.Prime] [RestrictedLieAlgebra R L p] (hL : ∀ x : L, p • x = 0) (x : L) :
    ad R L p hL x = LieAlgebra.ad R L x :=
  (rfl)

/-- The adjoint representation `LieAlgebra.ad R A : A →ₗ⁅R⁆ Module.End R A` of an associative
`R`-algebra of prime characteristic `p` as a morphism of restricted Lie algebras, without requiring
`CharP R p`. -/
def RestrictedLieHom.adOfAssociative (R A : Type*) [CommRing R] [Ring A] [Algebra R A]
    (p : ℕ) [Fact p.Prime] [CharP A p] :
    @RestrictedLieHom R p A (Module.End R A) _ _ _ (RestrictedLieAlgebra.ofAssociative R A p)
      _ _ (@RestrictedLieAlgebra.ofAssociative R (Module.End R A) _ _ _ p _
        (charP_of_injective_ringHom
          (f := (Algebra.lmul R A : A →ₐ[R] Module.End R A).toRingHom)
          Algebra.lmul_injective p)) :=
  @RestrictedLieHom.mk R p A (Module.End R A) _ _ _ (RestrictedLieAlgebra.ofAssociative R A p)
    _ _ (@RestrictedLieAlgebra.ofAssociative R (Module.End R A) _ _ _ p _
      (charP_of_injective_ringHom
        (f := (Algebra.lmul R A : A →ₐ[R] Module.End R A).toRingHom)
        Algebra.lmul_injective p))
    (LieAlgebra.ad R A) fun a => (RestrictedLieAlgebra.ofAssociative R A p).ad_pMap a

@[simp]
theorem RestrictedLieHom.adOfAssociative_apply (R A : Type*) [CommRing R] [Ring A] [Algebra R A]
    (p : ℕ) [Fact p.Prime] [CharP A p] (a : A) :
    adOfAssociative R A p a = LieAlgebra.ad R A a :=
  (rfl)

end Associative

end ExamplesDefs

end TauCeti

section Examples

attribute [local instance 100] LieRing.ofAssociativeRing

-- Witness: on a commutative associative algebra `A` of prime characteristic `p`,
-- `pMap a = a ^ p` is additive (`Λ_p = 0`).
example (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] (p : ℕ) [Fact p.Prime] [CharP A p]
    (a b : A) :
    (TauCeti.RestrictedLieAlgebra.ofAssociative R A p).pMap (a + b) =
      (TauCeti.RestrictedLieAlgebra.ofAssociative R A p).pMap a +
        (TauCeti.RestrictedLieAlgebra.ofAssociative R A p).pMap b := by
  let _ := TauCeti.RestrictedLieAlgebra.ofAssociative R A p
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  exact TauCeti.RestrictedLieAlgebra.pMap_add_of_lie_eq_zero hp
    (by rw [Ring.lie_def, mul_comm, sub_self])

-- Witness: on `M_2(ZMod p)` for an odd prime `p`, `pMap a = a ^ p` is not additive.
example (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    let e₁₂ : Matrix (Fin 2) (Fin 2) (ZMod p) := !![0, 1; 0, 0]
    let e₂₁ : Matrix (Fin 2) (Fin 2) (ZMod p) := !![0, 0; 1, 0]
    (e₁₂ + e₂₁) ^ p ≠ e₁₂ ^ p + e₂₁ ^ p := by
  intro e₁₂ e₂₁ h
  have hprime : p.Prime := Fact.out
  have hodd : Odd p := hprime.odd_of_ne_two hp
  have he12_sq : e₁₂ ^ 2 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [e₁₂, pow_two, Matrix.mul_apply]
  have he21_sq : e₂₁ ^ 2 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [e₂₁, pow_two, Matrix.mul_apply]
  have he12_pow : e₁₂ ^ p = 0 :=
    calc e₁₂ ^ p = e₁₂ ^ (2 + (p - 2)) := congrArg (e₁₂ ^ ·) (Nat.add_sub_of_le hprime.two_le).symm
      _ = e₁₂ ^ 2 * e₁₂ ^ (p - 2) := pow_add _ _ _
      _ = 0 := by rw [he12_sq, zero_mul]
  have he21_pow : e₂₁ ^ p = 0 :=
    calc e₂₁ ^ p = e₂₁ ^ (2 + (p - 2)) := congrArg (e₂₁ ^ ·) (Nat.add_sub_of_le hprime.two_le).symm
      _ = e₂₁ ^ 2 * e₂₁ ^ (p - 2) := pow_add _ _ _
      _ = 0 := by rw [he21_sq, zero_mul]
  have hsum_sq : (e₁₂ + e₂₁) ^ 2 = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [e₁₂, e₂₁, pow_two, Matrix.mul_apply]
  obtain ⟨k, hk⟩ := hodd
  have hsum_pow : (e₁₂ + e₂₁) ^ p = e₁₂ + e₂₁ :=
    calc (e₁₂ + e₂₁) ^ p = (e₁₂ + e₂₁) ^ (2 * k + 1) := congrArg ((e₁₂ + e₂₁) ^ ·) hk
      _ = ((e₁₂ + e₂₁) ^ 2) ^ k * (e₁₂ + e₂₁) := by rw [pow_succ, pow_mul]
      _ = e₁₂ + e₂₁ := by rw [hsum_sq, one_pow, one_mul]
  rw [hsum_pow, he12_pow, he21_pow, add_zero] at h
  have h01 : (e₁₂ + e₂₁) 0 1 = (0 : ZMod p) := by simpa using congrArg (fun M => M 0 1) h
  simp [e₁₂, e₂₁] at h01

-- Witness: on a nontrivial commutative ring `R` of prime characteristic `p`, `ofAbelianZero` and
-- `ofAssociative` are two distinct restricted Lie algebra structures on the same Lie algebra
-- (they differ at `1 : R`).
example (R : Type*) [CommRing R] [Nontrivial R] (p : ℕ) [Fact p.Prime] [CharP R p] :
    let _ : IsLieAbelian R := ⟨fun x y => by rw [Ring.lie_def, mul_comm, sub_self]⟩
    TauCeti.RestrictedLieAlgebra.ofAbelianZero R R p (Fact.out : p.Prime).ne_zero ≠
      TauCeti.RestrictedLieAlgebra.ofAssociative R R p := by
  intro _ h
  have h1 := congrArg (fun inst => inst.pMap (1 : R)) h
  simp only [TauCeti.RestrictedLieAlgebra.ofAbelianZero_pMap,
    TauCeti.RestrictedLieAlgebra.ofAssociative_pMap, one_pow] at h1
  exact zero_ne_one h1

end Examples
