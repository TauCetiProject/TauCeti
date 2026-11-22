/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Lie.Abelian
public import TauCeti.Algebra.Lie.Restricted.Jacobson
import TauCeti.Algebra.Lie.AdjointAction.Frobenius

/-!
# Restricted Lie algebras

A *restricted Lie algebra* (or *`p`-Lie algebra*, Jacobson 1941; Katz 1970, §5.0) over a
commutative ring `R` is a Lie algebra `L` over `R` of prime characteristic `p` (`p.Prime` and
pointwise `p`-torsion `∀ x : L, p • x = 0`, which holds automatically when `CharP R p`, while also
accommodating mixed-characteristic base rings `R` acting on `p`-torsion Lie algebras) equipped
with a `p`-map `pMap : L → L` (`x ↦ x^[p]`) satisfying:

1. `p`-homogeneity: `pMap (c • x) = c ^ p • pMap x` for `c : R`, `x : L`;
2. adjoint compatibility: `LieAlgebra.ad R L (pMap x) = LieAlgebra.ad R L x ^ p`;
3. Jacobson's additivity law:
   `pMap (x + y) = pMap x + pMap y + TauCeti.LieAlgebra.jacobson p x y`.

The `p`-map is genuine data rather than a property: on an abelian Lie algebra `R` of prime
characteristic `p` with `1 ≠ 0`, `pMap = 0` (`ofAbelianZero`) and `pMap x = x ^ p`
(`ofAssociative`) are two distinct restricted structures on the same Lie algebra.

We develop the basic structural theory: morphisms of restricted Lie algebras (`RestrictedLieHom`)
with identity and composition, restricted Lie subalgebras (`RestrictedLieSubalgebra`) with induced
restricted structure, containment order (`PartialOrder`, `OrderTop`, `OrderBot`,
`SemilatticeInf`), images (`RestrictedLieHom.range`), and surjective range restriction
(`RestrictedLieHom.rangeRestrict`), and restricted Lie ideals (`RestrictedLieIdeal`) with the same
order structure, kernels (`RestrictedLieHom.ker`), and the injectivity criterion
`RestrictedLieHom.ker_eq_bot`. We construct the standard examples: associative algebras of prime
characteristic `p` (`ofAssociative`), endomorphism algebras `Module.End R M` when `p` annihilates
`M` pointwise (`ofModuleEnd`, including trivial modules `M`), `p`-torsion abelian Lie algebras with
the zero `p`-map (`ofAbelianZero`), and the adjoint morphism `RestrictedLieHom.ad`.

## Main definitions

* `TauCeti.RestrictedLieAlgebra`: typeclass for a restricted Lie algebra structure on `L` over `R`.
* `TauCeti.RestrictedLieHom`: morphisms of restricted Lie algebras.
* `TauCeti.RestrictedLieSubalgebra`: Lie subalgebras closed under `pMap`.
* `TauCeti.RestrictedLieIdeal`: Lie ideals closed under `pMap`.
* `TauCeti.RestrictedLieAlgebra.ofAssociative`: the restricted Lie algebra structure `a ↦ a ^ p`
  on an associative algebra with `(p : A) = 0`.
* `TauCeti.RestrictedLieAlgebra.ofModuleEnd`: the restricted Lie algebra structure `f ↦ f ^ p` on
  `Module.End R M` when `p` annihilates `M` pointwise.
* `TauCeti.RestrictedLieAlgebra.ofAbelianZero`: the zero `p`-map on a `p`-torsion abelian Lie
  algebra for prime `p`.
* `TauCeti.RestrictedLieHom.ad`: `LieAlgebra.ad R L` as a restricted morphism for any restricted
  Lie algebra.

## References

* N. Jacobson, *Restricted Lie algebras of characteristic `p`*, Trans. Amer. Math. Soc. **50**
  (1941), 15–25.
* N. Jacobson, *Lie Algebras*, Interscience (1962), Chapter V, §7.
* N. M. Katz, *Nilpotent connections and the monodromy theorem: Applications of a result of
  Turrittin*, Publ. Math. IHÉS **39** (1970), §5.
-/

public section

namespace TauCeti

/-- A restricted Lie algebra (or `p`-Lie algebra, Jacobson 1941; Katz 1970, §5.0) over a
commutative ring `R`: a Lie algebra `L` of prime characteristic `p` (`p.Prime` and
`∀ x : L, p • x = 0`) equipped with a `p`-map `pMap : L → L` that is `p`-homogeneous, compatible
with the adjoint action, and satisfies Jacobson's additivity formula with
`TauCeti.LieAlgebra.jacobson`. -/
@[ext]
class RestrictedLieAlgebra (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] (p : ℕ) where
  /-- The characteristic `p` is prime. -/
  prime : p.Prime
  /-- Every element of `L` is annihilated by `p`. -/
  p_nsmul_eq_zero (x : L) : p • x = 0
  /-- The `p`-map `x ↦ x^[p]`. -/
  pMap : L → L
  /-- `p`-homogeneity: `pMap (c • x) = c ^ p • pMap x`. -/
  pMap_smul (c : R) (x : L) : pMap (c • x) = c ^ p • pMap x
  /-- Compatibility with the adjoint action: `ad (pMap x) = (ad x) ^ p`. -/
  ad_pMap (x : L) : LieAlgebra.ad R L (pMap x) = LieAlgebra.ad R L x ^ p
  /-- Jacobson's additivity formula for `pMap (x + y)`. -/
  pMap_add (x y : L) : pMap (x + y) = pMap x + pMap y + LieAlgebra.jacobson p x y

namespace RestrictedLieAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] {p : ℕ}
  [RestrictedLieAlgebra R L p]

/-- Evaluating `ad_pMap` on an element `y : L`: `⁅pMap x, y⁆ = (ad R L x ^ p) y`. -/
theorem pMap_lie (x y : L) :
    ⁅pMap (R := R) (p := p) x, y⁆ = (LieAlgebra.ad R L x ^ p) y := by
  have h := congrArg (fun f : Module.End R L => f y) (ad_pMap (R := R) (p := p) x)
  simpa only [LieAlgebra.ad_apply] using h

/-- `pMap 0 = 0`. -/
@[simp]
theorem pMap_zero : pMap (R := R) (p := p) (0 : L) = 0 := by
  have h := pMap_add (R := R) (p := p) (0 : L) (0 : L)
  rw [add_zero, LieAlgebra.jacobson_zero_left, add_zero] at h
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

/-- On commuting elements `x, y`, `pMap` is additive. -/
theorem pMap_add_of_lie_eq_zero {x y : L} (h : ⁅x, y⁆ = 0) :
    pMap (R := R) (p := p) (x + y) = pMap (R := R) (p := p) x + pMap (R := R) (p := p) y := by
  rw [pMap_add, LieAlgebra.jacobson_eq_zero_of_lie_eq_zero p h, add_zero]

/-- On commuting elements `x, y`, `pMap (x - y) = pMap x + (-1 : R) ^ p • pMap y`. -/
theorem pMap_sub_of_lie_eq_zero {x y : L} (h : ⁅x, y⁆ = 0) :
    pMap (R := R) (p := p) (x - y) =
      pMap (R := R) (p := p) x + (-1 : R) ^ p • pMap (R := R) (p := p) y := by
  rw [sub_eq_add_neg, pMap_add_of_lie_eq_zero (by rw [lie_neg, h, neg_zero]), pMap_neg]

/-- In an abelian restricted Lie algebra, `pMap` is additive. -/
theorem pMap_add_of_isLieAbelian [IsLieAbelian L] (x y : L) :
    pMap (R := R) (p := p) (x + y) = pMap (R := R) (p := p) x + pMap (R := R) (p := p) y :=
  pMap_add_of_lie_eq_zero (trivial_lie_zero L L x y)

/-- On a finite family of pairwise commuting elements, `pMap` commutes with the finite sum. -/
theorem pMap_sum_of_lie_eq_zero {ι : Type*} {s : Finset ι} {f : ι → L}
    (h : (s : Set ι).Pairwise fun i j => ⁅f i, f j⁆ = 0) :
    pMap (R := R) (p := p) (∑ i ∈ s, f i) = ∑ i ∈ s, pMap (R := R) (p := p) (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.coe_insert] at h
    have h' := Set.pairwise_insert.mp h
    have hcomm : ⁅f a, ∑ i ∈ s, f i⁆ = 0 := by
      rw [lie_sum]
      exact Finset.sum_eq_zero fun i hi => (h'.2 i hi (ne_of_mem_of_not_mem hi ha).symm).1
    rw [Finset.sum_insert ha, pMap_add_of_lie_eq_zero hcomm, ih h'.1, Finset.sum_insert ha]

/-- In an abelian restricted Lie algebra, `pMap` commutes with finite sums. -/
theorem pMap_sum_of_isLieAbelian [IsLieAbelian L] {ι : Type*} (s : Finset ι) (f : ι → L) :
    pMap (R := R) (p := p) (∑ i ∈ s, f i) = ∑ i ∈ s, pMap (R := R) (p := p) (f i) :=
  pMap_sum_of_lie_eq_zero fun _ _ _ _ _ => trivial_lie_zero L L _ _

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

instance : LinearMapClass (RestrictedLieHom R p L L') R L L' where
  map_add f x y := f.toLieHom.map_add x y
  map_smulₛₗ f c x := f.toLieHom.map_smul c x

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

/-- A restricted Lie algebra morphism commutes with the `p`-map `RestrictedLieAlgebra.pMap`. -/
@[simp]
theorem map_pMap (f : RestrictedLieHom R p L L') (x : L) :
    f (RestrictedLieAlgebra.pMap (R := R) (p := p) x) =
      RestrictedLieAlgebra.pMap (R := R) (p := p) (f x) :=
  f.map_pMap' x

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

/-- A restricted Lie subalgebra is closed under `RestrictedLieAlgebra.pMap`. -/
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

/-- A restricted Lie subalgebra inherits a restricted Lie algebra structure from the ambient
restricted Lie algebra. -/
instance instRestrictedLieAlgebra (S : RestrictedLieSubalgebra R p L) :
    RestrictedLieAlgebra R S p where
  prime := RestrictedLieAlgebra.prime (R := R) (L := L) (p := p)
  p_nsmul_eq_zero x := Subtype.ext (RestrictedLieAlgebra.p_nsmul_eq_zero (R := R) (p := p) (x : L))
  pMap x := ⟨RestrictedLieAlgebra.pMap (R := R) (p := p) (x : L), S.pMap_mem x.property⟩
  pMap_smul c x := by
    apply Subtype.ext
    exact RestrictedLieAlgebra.pMap_smul c (x : L)
  ad_pMap x := by
    refine LinearMap.ext fun y => Subtype.ext ?_
    rw [LieAlgebra.ad_apply, coe_lie]
    exact (RestrictedLieAlgebra.pMap_lie (R := R) (p := p) (x : L) (y : L)).trans
      (LieSubalgebra.coe_ad_pow (R := R) (L := L) S.toLieSubalgebra x y p).symm
  pMap_add x y := by
    refine Subtype.ext ?_
    have hincl : ((LieAlgebra.jacobson p x y : S) : L) = LieAlgebra.jacobson p (x : L) (y : L) :=
      LieHom.map_jacobson S.toLieSubalgebra.incl p x y
    dsimp only
    rw [coe_add, coe_add, coe_add, hincl]
    exact RestrictedLieAlgebra.pMap_add (R := R) (p := p) (x : L) (y : L)

/-- The `p`-map on a restricted Lie subalgebra coerces to the ambient `p`-map. -/
@[simp]
theorem coe_pMap (S : RestrictedLieSubalgebra R p L) (x : S) :
    ((RestrictedLieAlgebra.pMap (R := R) (p := p) x : S) : L) =
      RestrictedLieAlgebra.pMap (R := R) (p := p) (x : L) :=
  (rfl)

/-- The canonical inclusion `S → L` of a restricted Lie subalgebra as a restricted morphism. -/
def incl (S : RestrictedLieSubalgebra R p L) : RestrictedLieHom R p S L where
  toLieHom := S.toLieSubalgebra.incl
  map_pMap' _ := rfl

@[simp]
theorem incl_apply (S : RestrictedLieSubalgebra R p L) (x : S) : S.incl x = x :=
  (rfl)

@[simp]
theorem toLieHom_incl (S : RestrictedLieSubalgebra R p L) :
    S.incl.toLieHom = S.toLieSubalgebra.incl :=
  (rfl)

theorem incl_injective (S : RestrictedLieSubalgebra R p L) : Function.Injective S.incl :=
  Subtype.val_injective

instance : PartialOrder (RestrictedLieSubalgebra R p L) :=
  .ofSetLike (RestrictedLieSubalgebra R p L)

theorem le_def {S T : RestrictedLieSubalgebra R p L} : S ≤ T ↔ (S : Set L) ⊆ T :=
  Iff.rfl

@[simp]
theorem toLieSubalgebra_le_toLieSubalgebra {S T : RestrictedLieSubalgebra R p L} :
    S.toLieSubalgebra ≤ T.toLieSubalgebra ↔ S ≤ T :=
  Iff.rfl

@[simp]
theorem toLieSubalgebra_inj {S T : RestrictedLieSubalgebra R p L} :
    S.toLieSubalgebra = T.toLieSubalgebra ↔ S = T :=
  toLieSubalgebra_injective.eq_iff

instance : OrderTop (RestrictedLieSubalgebra R p L) where
  top :=
    { toLieSubalgebra := ⊤
      pMap_mem' := fun _ => Set.mem_univ _ }
  le_top _ _ _ := Set.mem_univ _

@[simp]
theorem toLieSubalgebra_top :
    ((⊤ : RestrictedLieSubalgebra R p L).toLieSubalgebra) = ⊤ :=
  (rfl)

@[simp]
theorem mem_top (x : L) : x ∈ (⊤ : RestrictedLieSubalgebra R p L) :=
  Set.mem_univ x

instance : OrderBot (RestrictedLieSubalgebra R p L) where
  bot :=
    { toLieSubalgebra := ⊥
      pMap_mem' := fun {x} hx => by
        have hx0 : x = 0 := (LieSubalgebra.mem_bot (R := R) x).mp hx
        exact (LieSubalgebra.mem_bot (R := R) _).mpr <| by
          rw [hx0, RestrictedLieAlgebra.pMap_zero] }
  bot_le S x hx := by
    have hx0 : x = 0 := (LieSubalgebra.mem_bot (R := R) x).mp hx
    rw [hx0]
    exact S.zero_mem

@[simp]
theorem toLieSubalgebra_bot :
    ((⊥ : RestrictedLieSubalgebra R p L).toLieSubalgebra) = ⊥ :=
  (rfl)

@[simp]
theorem mem_bot {x : L} : x ∈ (⊥ : RestrictedLieSubalgebra R p L) ↔ x = 0 :=
  LieSubalgebra.mem_bot x

instance : SemilatticeInf (RestrictedLieSubalgebra R p L) where
  inf S T :=
    { toLieSubalgebra := S.toLieSubalgebra ⊓ T.toLieSubalgebra
      pMap_mem' := fun ⟨hxS, hxT⟩ => ⟨S.pMap_mem hxS, T.pMap_mem hxT⟩ }
  inf_le_left _ _ _ := And.left
  inf_le_right _ _ _ := And.right
  le_inf _ _ _ h₁₂ h₁₃ _ hx := ⟨h₁₂ hx, h₁₃ hx⟩

@[simp]
theorem toLieSubalgebra_inf (S T : RestrictedLieSubalgebra R p L) :
    (S ⊓ T).toLieSubalgebra = S.toLieSubalgebra ⊓ T.toLieSubalgebra :=
  (rfl)

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
theorem RestrictedLieHom.toLieSubalgebra_range {R : Type*} {p : ℕ} {L L' : Type*} [CommRing R]
    [LieRing L] [LieAlgebra R L] [RestrictedLieAlgebra R L p] [LieRing L'] [LieAlgebra R L']
    [RestrictedLieAlgebra R L' p] (f : RestrictedLieHom R p L L') :
    f.range.toLieSubalgebra = f.toLieHom.range :=
  (rfl)

@[simp]
theorem RestrictedLieHom.mem_range {R : Type*} {p : ℕ} {L L' : Type*} [CommRing R] [LieRing L]
    [LieAlgebra R L] [RestrictedLieAlgebra R L p] [LieRing L'] [LieAlgebra R L']
    [RestrictedLieAlgebra R L' p] (f : RestrictedLieHom R p L L') {y : L'} :
    y ∈ f.range ↔ ∃ x : L, f x = y :=
  Iff.rfl

/-- Any image `f x` lies in `f.range`. -/
theorem RestrictedLieHom.mem_range_self {R : Type*} {p : ℕ} {L L' : Type*} [CommRing R]
    [LieRing L] [LieAlgebra R L] [RestrictedLieAlgebra R L p] [LieRing L'] [LieAlgebra R L']
    [RestrictedLieAlgebra R L' p] (f : RestrictedLieHom R p L L') (x : L) :
    f x ∈ f.range :=
  ⟨x, rfl⟩

/-- Restrict a restricted Lie algebra morphism to a surjective morphism onto its range. -/
def RestrictedLieHom.rangeRestrict {R : Type*} {p : ℕ} {L L' : Type*} [CommRing R] [LieRing L]
    [LieAlgebra R L] [RestrictedLieAlgebra R L p] [LieRing L'] [LieAlgebra R L']
    [RestrictedLieAlgebra R L' p] (f : RestrictedLieHom R p L L') :
    RestrictedLieHom R p L f.range where
  toLieHom := f.toLieHom.rangeRestrict
  map_pMap' x := Subtype.ext (f.map_pMap x)

@[simp]
theorem RestrictedLieHom.rangeRestrict_apply {R : Type*} {p : ℕ} {L L' : Type*} [CommRing R]
    [LieRing L] [LieAlgebra R L] [RestrictedLieAlgebra R L p] [LieRing L'] [LieAlgebra R L']
    [RestrictedLieAlgebra R L' p] (f : RestrictedLieHom R p L L') (x : L) :
    f.rangeRestrict x = ⟨f x, f.mem_range_self x⟩ :=
  (rfl)

theorem RestrictedLieHom.coe_rangeRestrict_apply {R : Type*} {p : ℕ} {L L' : Type*} [CommRing R]
    [LieRing L] [LieAlgebra R L] [RestrictedLieAlgebra R L p] [LieRing L'] [LieAlgebra R L']
    [RestrictedLieAlgebra R L' p] (f : RestrictedLieHom R p L L') (x : L) :
    (f.rangeRestrict x : L') = f x :=
  (rfl)

@[simp]
theorem RestrictedLieHom.incl_comp_rangeRestrict {R : Type*} {p : ℕ} {L L' : Type*} [CommRing R]
    [LieRing L] [LieAlgebra R L] [RestrictedLieAlgebra R L p] [LieRing L'] [LieAlgebra R L']
    [RestrictedLieAlgebra R L' p] (f : RestrictedLieHom R p L L') :
    f.range.incl.comp f.rangeRestrict = f := by
  ext x
  rfl

/-- The range restriction of a restricted Lie algebra morphism is surjective. -/
theorem RestrictedLieHom.surjective_rangeRestrict {R : Type*} {p : ℕ} {L L' : Type*} [CommRing R]
    [LieRing L] [LieAlgebra R L] [RestrictedLieAlgebra R L p] [LieRing L'] [LieAlgebra R L']
    [RestrictedLieAlgebra R L' p] (f : RestrictedLieHom R p L L') :
    Function.Surjective f.rangeRestrict := by
  rintro ⟨y, hy⟩
  rw [mem_range] at hy
  obtain ⟨x, rfl⟩ := hy
  exact ⟨x, rfl⟩

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

/-- A restricted Lie ideal is closed under `RestrictedLieAlgebra.pMap`. -/
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
@[expose] def toRestrictedLieSubalgebra (I : RestrictedLieIdeal R p L) :
    RestrictedLieSubalgebra R p L where
  toLieSubalgebra := I.toLieIdeal.toLieSubalgebra
  pMap_mem' := I.pMap_mem'

@[simp]
theorem mem_toRestrictedLieSubalgebra (I : RestrictedLieIdeal R p L) {x : L} :
    x ∈ I.toRestrictedLieSubalgebra ↔ x ∈ I :=
  Iff.rfl

instance instLieRing (I : RestrictedLieIdeal R p L) : LieRing I :=
  I.toRestrictedLieSubalgebra.instLieRing

instance instLieAlgebra (I : RestrictedLieIdeal R p L) : LieAlgebra R I :=
  I.toRestrictedLieSubalgebra.instLieAlgebra

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

/-- A restricted Lie ideal inherits a restricted Lie algebra structure via its underlying
restricted Lie subalgebra `I.toRestrictedLieSubalgebra`, reusing the same `LieRing` and
`LieAlgebra` instances as `instLieRing` and `instLieAlgebra`. -/
instance instRestrictedLieAlgebra (I : RestrictedLieIdeal R p L) :
    RestrictedLieAlgebra R I p :=
  inferInstanceAs <| RestrictedLieAlgebra R I.toRestrictedLieSubalgebra p

/-- The `p`-map on a restricted Lie ideal coerces to the ambient `p`-map. -/
@[simp]
theorem coe_pMap (I : RestrictedLieIdeal R p L) (x : I) :
    ((RestrictedLieAlgebra.pMap (R := R) (p := p) x : I) : L) =
      RestrictedLieAlgebra.pMap (R := R) (p := p) (x : L) :=
  (rfl)

/-- The canonical inclusion `I → L` of a restricted Lie ideal as a restricted morphism. -/
def incl (I : RestrictedLieIdeal R p L) : RestrictedLieHom R p I L where
  toLieHom := I.toLieIdeal.incl
  map_pMap' _ := rfl

@[simp]
theorem incl_apply (I : RestrictedLieIdeal R p L) (x : I) : I.incl x = x :=
  (rfl)

@[simp]
theorem toLieHom_incl (I : RestrictedLieIdeal R p L) : I.incl.toLieHom = I.toLieIdeal.incl :=
  (rfl)

theorem incl_injective (I : RestrictedLieIdeal R p L) : Function.Injective I.incl :=
  Subtype.val_injective

instance : PartialOrder (RestrictedLieIdeal R p L) :=
  .ofSetLike (RestrictedLieIdeal R p L)

theorem le_def {I J : RestrictedLieIdeal R p L} : I ≤ J ↔ (I : Set L) ⊆ J :=
  Iff.rfl

@[simp]
theorem toLieIdeal_le_toLieIdeal {I J : RestrictedLieIdeal R p L} :
    I.toLieIdeal ≤ J.toLieIdeal ↔ I ≤ J :=
  Iff.rfl

@[simp]
theorem toLieIdeal_inj {I J : RestrictedLieIdeal R p L} :
    I.toLieIdeal = J.toLieIdeal ↔ I = J :=
  toLieIdeal_injective.eq_iff

instance : OrderTop (RestrictedLieIdeal R p L) where
  top :=
    { toLieIdeal := ⊤
      pMap_mem' := fun _ => trivial }
  le_top _ _ _ := trivial

@[simp]
theorem toLieIdeal_top : ((⊤ : RestrictedLieIdeal R p L).toLieIdeal) = ⊤ :=
  (rfl)

@[simp]
theorem mem_top (x : L) : x ∈ (⊤ : RestrictedLieIdeal R p L) :=
  trivial

instance : OrderBot (RestrictedLieIdeal R p L) where
  bot :=
    { toLieIdeal := ⊥
      pMap_mem' := fun hx => by
        rw [LieSubmodule.mem_bot] at hx ⊢
        rw [hx, RestrictedLieAlgebra.pMap_zero] }
  bot_le I x hx := by
    have hx0 : x = 0 := (LieSubmodule.mem_bot x).mp hx
    rw [hx0]
    exact I.zero_mem

@[simp]
theorem toLieIdeal_bot : ((⊥ : RestrictedLieIdeal R p L).toLieIdeal) = ⊥ :=
  (rfl)

@[simp]
theorem mem_bot {x : L} : x ∈ (⊥ : RestrictedLieIdeal R p L) ↔ x = 0 :=
  LieSubmodule.mem_bot x

instance : SemilatticeInf (RestrictedLieIdeal R p L) where
  inf I J :=
    { toLieIdeal := I.toLieIdeal ⊓ J.toLieIdeal
      pMap_mem' := fun ⟨hxI, hxJ⟩ => ⟨I.pMap_mem hxI, J.pMap_mem hxJ⟩ }
  inf_le_left _ _ _ := And.left
  inf_le_right _ _ _ := And.right
  le_inf _ _ _ h₁₂ h₁₃ _ hx := ⟨h₁₂ hx, h₁₃ hx⟩

@[simp]
theorem toLieIdeal_inf (I J : RestrictedLieIdeal R p L) :
    (I ⊓ J).toLieIdeal = I.toLieIdeal ⊓ J.toLieIdeal :=
  (rfl)

@[simp]
theorem mem_inf {I J : RestrictedLieIdeal R p L} {x : L} :
    x ∈ I ⊓ J ↔ x ∈ I ∧ x ∈ J :=
  Iff.rfl

end RestrictedLieIdeal

/-- The kernel of a restricted Lie algebra morphism, as a restricted Lie ideal. -/
def RestrictedLieHom.ker {R : Type*} {p : ℕ} {L L' : Type*} [CommRing R] [LieRing L]
    [LieAlgebra R L] [RestrictedLieAlgebra R L p] [LieRing L'] [LieAlgebra R L']
    [RestrictedLieAlgebra R L' p] (f : RestrictedLieHom R p L L') :
    RestrictedLieIdeal R p L where
  toLieIdeal := f.toLieHom.ker
  pMap_mem' {x} hx := by
    rw [LieHom.mem_ker, RestrictedLieHom.toLieHom_apply] at hx ⊢
    rw [f.map_pMap, hx, RestrictedLieAlgebra.pMap_zero]

@[simp]
theorem RestrictedLieHom.toLieIdeal_ker {R : Type*} {p : ℕ} {L L' : Type*} [CommRing R]
    [LieRing L] [LieAlgebra R L] [RestrictedLieAlgebra R L p] [LieRing L'] [LieAlgebra R L']
    [RestrictedLieAlgebra R L' p] (f : RestrictedLieHom R p L L') :
    f.ker.toLieIdeal = f.toLieHom.ker :=
  (rfl)

@[simp]
theorem RestrictedLieHom.mem_ker {R : Type*} {p : ℕ} {L L' : Type*} [CommRing R] [LieRing L]
    [LieAlgebra R L] [RestrictedLieAlgebra R L p] [LieRing L'] [LieAlgebra R L']
    [RestrictedLieAlgebra R L' p] (f : RestrictedLieHom R p L L') {x : L} :
    x ∈ f.ker ↔ f x = 0 :=
  LieHom.mem_ker (f := f.toLieHom)

/-- A restricted Lie algebra morphism has trivial kernel if and only if it is injective. -/
theorem RestrictedLieHom.ker_eq_bot {R : Type*} {p : ℕ} {L L' : Type*} [CommRing R] [LieRing L]
    [LieAlgebra R L] [RestrictedLieAlgebra R L p] [LieRing L'] [LieAlgebra R L']
    [RestrictedLieAlgebra R L' p] (f : RestrictedLieHom R p L L') :
    f.ker = ⊥ ↔ Function.Injective f := by
  rw [← RestrictedLieIdeal.toLieIdeal_inj, toLieIdeal_ker, RestrictedLieIdeal.toLieIdeal_bot,
    LieHom.ker_eq_bot, coe_toLieHom]

end Ideal

section ExamplesDefs

/-- The trivial (zero) restricted Lie algebra structure on a `p`-torsion abelian Lie algebra for
prime `p`. -/
@[instance_reducible]
def RestrictedLieAlgebra.ofAbelianZero (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
    [IsLieAbelian L] (p : ℕ) [Fact p.Prime] (hL : ∀ x : L, p • x = 0) :
    RestrictedLieAlgebra R L p where
  prime := Fact.out
  p_nsmul_eq_zero := hL
  pMap _ := 0
  pMap_smul _ _ := (smul_zero _).symm
  ad_pMap x := by
    have h0 : LieAlgebra.ad R L x = 0 := by
      ext y
      exact trivial_lie_zero L L x y
    rw [map_zero, h0, zero_pow (Fact.out : p.Prime).ne_zero]
  pMap_add x y := by
    rw [add_zero, LieAlgebra.jacobson_eq_zero_of_lie_eq_zero p (trivial_lie_zero L L x y),
      add_zero]

@[simp]
theorem RestrictedLieAlgebra.ofAbelianZero_pMap (R L : Type*) [CommRing R] [LieRing L]
    [LieAlgebra R L] [IsLieAbelian L] (p : ℕ) [Fact p.Prime] (hL : ∀ x : L, p • x = 0)
    (x : L) :
    (ofAbelianZero R L p hL).pMap x = 0 :=
  (rfl)

section Associative

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The restricted Lie algebra structure `a ↦ a ^ p` on an associative `R`-algebra `A` for prime
`p` with `(p : A) = 0` (including the zero ring). Defined as a `def` rather than a global `instance`
because `LieRing.ofAssociativeRing` is a local instance. -/
@[instance_reducible]
def RestrictedLieAlgebra.ofAssociative (R A : Type*) [CommRing R] [Ring A] [Algebra R A]
    (p : ℕ) [Fact p.Prime] (hpA : (p : A) = 0) : RestrictedLieAlgebra R A p where
  prime := Fact.out
  p_nsmul_eq_zero a := by rw [nsmul_eq_mul, hpA, zero_mul]
  pMap a := a ^ p
  pMap_smul c a := smul_pow c a p
  ad_pMap a := by
    rcases subsingleton_or_nontrivial A with _ | _
    · exact Subsingleton.elim _ _
    · have : CharP A p := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hpA
      have : ExpChar A p := ExpChar.prime Fact.out
      simpa only [pow_one] using TauCeti.LieAlgebra.ad_pow_expChar_pow (R := R) p a 1
  pMap_add a b := by
    rcases subsingleton_or_nontrivial A with _ | _
    · exact Subsingleton.elim _ _
    · have : CharP A p := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hpA
      have : ExpChar A p := ExpChar.prime Fact.out
      exact LieAlgebra.add_pow_eq_jacobson p a b

@[simp]
theorem RestrictedLieAlgebra.ofAssociative_pMap (R A : Type*) [CommRing R] [Ring A] [Algebra R A]
    (p : ℕ) [Fact p.Prime] (hpA : (p : A) = 0) (a : A) :
    (ofAssociative R A p hpA).pMap a = a ^ p :=
  (rfl)

/-- The restricted Lie algebra structure `f ↦ f ^ p` on `Module.End R M` for prime `p`, whenever
`p` annihilates `M` pointwise (`∀ m : M, p • m = 0`). Valid for every such `R`-module `M`,
including trivial modules and modules over mixed-characteristic base rings `R`. -/
@[instance_reducible]
def RestrictedLieAlgebra.ofModuleEnd (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (p : ℕ) [Fact p.Prime] (hM : ∀ m : M, p • m = 0) :
    RestrictedLieAlgebra R (Module.End R M) p :=
  ofAssociative R (Module.End R M) p (by ext m; simp [hM m])

theorem RestrictedLieAlgebra.ofModuleEnd_pMap (R M : Type*) [CommRing R] [AddCommGroup M]
    [Module R M] (p : ℕ) [Fact p.Prime] (hM : ∀ m : M, p • m = 0) (f : Module.End R M) :
    (ofModuleEnd R M p hM).pMap f = f ^ p :=
  (rfl)

/-- `ofModuleEnd` is definitionally `ofAssociative` on `Module.End R M`. -/
theorem RestrictedLieAlgebra.ofModuleEnd_eq_ofAssociative (R M : Type*) [CommRing R]
    [AddCommGroup M] [Module R M] (p : ℕ) [Fact p.Prime] (hM : ∀ m : M, p • m = 0)
    (hpEnd : (p : Module.End R M) = 0) :
    ofModuleEnd R M p hM = ofAssociative R (Module.End R M) p hpEnd :=
  (rfl)

/-- The adjoint representation `LieAlgebra.ad R L : L →ₗ⁅R⁆ Module.End R L` of a restricted Lie
algebra, as a morphism of restricted Lie algebras into `ofModuleEnd`. -/
def RestrictedLieHom.ad (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] (p : ℕ)
    [RestrictedLieAlgebra R L p] :
    @RestrictedLieHom R p L (Module.End R L) _ _ _ _ _ _
      (@RestrictedLieAlgebra.ofModuleEnd R L _ _ _ p
        ⟨RestrictedLieAlgebra.prime (R := R) (L := L) (p := p)⟩
        (RestrictedLieAlgebra.p_nsmul_eq_zero (R := R) (p := p))) :=
  @RestrictedLieHom.mk R p L (Module.End R L) _ _ _ _ _ _
    (@RestrictedLieAlgebra.ofModuleEnd R L _ _ _ p
      ⟨RestrictedLieAlgebra.prime (R := R) (L := L) (p := p)⟩
      (RestrictedLieAlgebra.p_nsmul_eq_zero (R := R) (p := p)))
    (LieAlgebra.ad R L)
    (fun x => RestrictedLieAlgebra.ad_pMap (R := R) (p := p) x)

@[simp]
theorem RestrictedLieHom.ad_apply (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] (p : ℕ)
    [RestrictedLieAlgebra R L p] (x : L) :
    ad R L p x = LieAlgebra.ad R L x :=
  (rfl)

@[simp]
theorem RestrictedLieHom.toLieHom_ad (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
    (p : ℕ) [RestrictedLieAlgebra R L p] :
    @RestrictedLieHom.toLieHom R p L (Module.End R L) _ _ _ _ _ _
      (@RestrictedLieAlgebra.ofModuleEnd R L _ _ _ p
        ⟨RestrictedLieAlgebra.prime (R := R) (L := L) (p := p)⟩
        (RestrictedLieAlgebra.p_nsmul_eq_zero (R := R) (p := p)))
      (ad R L p) = LieAlgebra.ad R L :=
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
    (TauCeti.RestrictedLieAlgebra.ofAssociative R A p (CharP.cast_eq_zero A p)).pMap (a + b) =
      (TauCeti.RestrictedLieAlgebra.ofAssociative R A p (CharP.cast_eq_zero A p)).pMap a +
        (TauCeti.RestrictedLieAlgebra.ofAssociative R A p (CharP.cast_eq_zero A p)).pMap b := by
  let _ := TauCeti.RestrictedLieAlgebra.ofAssociative R A p (CharP.cast_eq_zero A p)
  exact TauCeti.RestrictedLieAlgebra.pMap_add_of_lie_eq_zero
    (by rw [Ring.lie_def, mul_comm, sub_self])

-- Witness: on a nontrivial commutative ring `R` of prime characteristic `p`, `ofAbelianZero` and
-- `ofAssociative` are two distinct restricted Lie algebra structures on the same Lie algebra
-- (they differ at `1 : R`).
example (R : Type*) [CommRing R] [Nontrivial R] (p : ℕ) [Fact p.Prime] [CharP R p] :
    let _ : IsLieAbelian R := ⟨fun x y => by rw [Ring.lie_def, mul_comm, sub_self]⟩
    TauCeti.RestrictedLieAlgebra.ofAbelianZero R R p
        (fun x => by rw [nsmul_eq_mul, CharP.cast_eq_zero R p, zero_mul]) ≠
      TauCeti.RestrictedLieAlgebra.ofAssociative R R p (CharP.cast_eq_zero R p) := by
  intro _ h
  have h1 := congrArg (fun inst => inst.pMap (1 : R)) h
  simp only [TauCeti.RestrictedLieAlgebra.ofAbelianZero_pMap,
    TauCeti.RestrictedLieAlgebra.ofAssociative_pMap, one_pow] at h1
  exact zero_ne_one h1

end Examples
