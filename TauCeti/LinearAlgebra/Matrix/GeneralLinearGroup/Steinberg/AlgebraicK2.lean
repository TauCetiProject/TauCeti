/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Steinberg.Stable

/-!
# Classical algebraic `K₂`

For an associative unital ring `R`, Milnor's **algebraic `K₂`** group `AlgebraicK2 R` is the kernel
of the canonical homomorphism `SteinbergGroup.toStableGL R : SteinbergGroup ℕ R →* GL_∞(R)` (equally
the kernel of the universal central extension `toStableElementary R : St(R) →* E_∞(R)`).

By the centrality theorem `TauCeti.SteinbergGroup.ker_toStableGL_eq_center`, `AlgebraicK2 R`
coincides with the center of `SteinbergGroup ℕ R` and is therefore an abelian group. It fits into
the four-term exact sequence
`1 → K₂(R) → St(R) → GL_∞(R) → K₁(R) → 1`,
is functorial in ring homomorphisms, and preserves binary products of rings.

## Main definitions

* `TauCeti.AlgebraicK2`: Milnor's algebraic `K₂(R)`, the kernel of
  `SteinbergGroup.toStableGL R : St(R) →* GL_∞(R)`.
* `TauCeti.AlgebraicK2.subtype`: the canonical inclusion `K₂(R) →* St(R)`.
* `TauCeti.AlgebraicK2.centerEquiv`: the identification `K₂(R) ≃* Subgroup.center (St(R))`.
* `TauCeti.AlgebraicK2.map`: the homomorphism `K₂(R) →* K₂(S)` induced by a ring homomorphism.
* `TauCeti.AlgebraicK2.prodEquiv`: the product isomorphism `K₂(R × S) ≃* K₂(R) × K₂(S)`.

## Main results

* `TauCeti.AlgebraicK2.instCommGroup`: `AlgebraicK2 R` is a commutative group.
* `TauCeti.AlgebraicK2.subtype_injective`, `TauCeti.AlgebraicK2.range_subtype`,
  `TauCeti.SteinbergGroup.range_toStableGL_eq_ker_abelianization`: exactness of
  `1 → K₂(R) → St(R) → GL_∞(R) → K₁(R) → 1`.
* `TauCeti.AlgebraicK2.map_id`, `TauCeti.AlgebraicK2.map_comp`, `TauCeti.AlgebraicK2.map_map`:
  functoriality of `AlgebraicK2`.

## References

* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971), §5,
  Definition on p. 41 and Theorem 5.1.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, §5, Definition 5.2 and Corollary 5.6.1.
-/

public section

noncomputable section

namespace TauCeti

variable (R : Type*) [Ring R]

/-- **Algebraic `K₂`** of an associative unital ring `R`: the kernel of the canonical homomorphism
`SteinbergGroup.toStableGL R : St(R) →* GL_∞(R)`. -/
abbrev AlgebraicK2 : Type _ :=
  (SteinbergGroup.toStableGL R).ker

namespace AlgebraicK2

variable {R}

/-- `AlgebraicK2 R` is a commutative group because `ker (toStableGL R)` is central in
`SteinbergGroup ℕ R`. -/
instance instCommGroup : CommGroup (AlgebraicK2 R) :=
  { (inferInstance : Group (AlgebraicK2 R)) with
    mul_comm a b := Subtype.ext <|
      Subgroup.mem_center_iff.mp (SteinbergGroup.ker_toStableGL_le_center b.2) a.1 }

variable (R) in
/-- The canonical inclusion `K₂(R) →* St(R)`. -/
def subtype : AlgebraicK2 R →* SteinbergGroup ℕ R :=
  (SteinbergGroup.toStableGL R).ker.subtype

/-- Applying `AlgebraicK2.subtype` returns the underlying element of `SteinbergGroup ℕ R`. -/
@[simp]
theorem coe_subtype (x : AlgebraicK2 R) : subtype R x = (x : SteinbergGroup ℕ R) :=
  (rfl)

/-- The canonical inclusion `K₂(R) →* St(R)` is injective. -/
theorem subtype_injective : Function.Injective (subtype R) :=
  Subtype.val_injective

/-- The image of `K₂(R) →* St(R)` is `ker (toStableGL R)`. -/
theorem range_subtype : (subtype R).range = (SteinbergGroup.toStableGL R).ker :=
  Subgroup.range_subtype _

/-- Every element of `K₂(R)` is central in `SteinbergGroup ℕ R`. -/
theorem subtype_mem_center (x : AlgebraicK2 R) :
    subtype R x ∈ Subgroup.center (SteinbergGroup ℕ R) :=
  SteinbergGroup.ker_toStableGL_le_center x.2

/-- The image of `K₂(R) →* St(R)` is the entire center of `SteinbergGroup ℕ R`. -/
theorem range_subtype_eq_center :
    (subtype R).range = Subgroup.center (SteinbergGroup ℕ R) := by
  rw [range_subtype, SteinbergGroup.ker_toStableGL_eq_center]

/-- Composing `toStableGL R` with `AlgebraicK2.subtype R` yields the trivial homomorphism. -/
@[simp]
theorem toStableGL_comp_subtype : (SteinbergGroup.toStableGL R).comp (subtype R) = 1 := by
  ext x
  exact MonoidHom.mem_ker.mp x.2

variable (R) in
/-- Identification of `AlgebraicK2 R` with the center of `SteinbergGroup ℕ R`. -/
def centerEquiv : AlgebraicK2 R ≃* Subgroup.center (SteinbergGroup ℕ R) :=
  MulEquiv.subgroupCongr SteinbergGroup.ker_toStableGL_eq_center

/-- `centerEquiv` preserves the underlying element of `SteinbergGroup ℕ R`. -/
@[simp]
theorem coe_centerEquiv (x : AlgebraicK2 R) :
    (centerEquiv R x : SteinbergGroup ℕ R) = x :=
  (rfl)

/-! ## Functoriality -/

section Map

variable {S T : Type*} [Ring S] [Ring T]

/-- The homomorphism `K₂(R) →* K₂(S)` induced by a ring homomorphism `f : R →+* S`. -/
def map (f : R →+* S) : AlgebraicK2 R →* AlgebraicK2 S :=
  ((SteinbergGroup.map f).comp (subtype R)).codRestrict (SteinbergGroup.toStableGL S).ker
    fun x => SteinbergGroup.map_mem_ker_toStableGL f x.2

/-- The underlying element of `AlgebraicK2.map f x` in `St(S)` is `SteinbergGroup.map f x`. -/
@[simp]
theorem coe_map (f : R →+* S) (x : AlgebraicK2 R) :
    (map f x : SteinbergGroup ℕ S) = SteinbergGroup.map f x :=
  (rfl)

/-- `AlgebraicK2.subtype` is natural in the ring. -/
theorem subtype_comp_map (f : R →+* S) :
    (subtype S).comp (map f) = (SteinbergGroup.map f).comp (subtype R) :=
  (rfl)

/-- The identity ring homomorphism induces the identity on `K₂`. -/
@[simp]
theorem map_id : map (RingHom.id R) = MonoidHom.id (AlgebraicK2 R) := by
  ext x
  simp

/-- `AlgebraicK2.map` respects composition of ring homomorphisms. -/
theorem map_comp (f : R →+* S) (g : S →+* T) :
    map (g.comp f) = (map g).comp (map f) := by
  ext x
  simp

/-- Applying `AlgebraicK2.map f` and then `AlgebraicK2.map g` agrees with
`AlgebraicK2.map (g.comp f)`. -/
@[simp]
theorem map_map (f : R →+* S) (g : S →+* T) (x : AlgebraicK2 R) :
    map g (map f x) = map (g.comp f) x := by
  rw [map_comp, MonoidHom.comp_apply]

/-- A ring isomorphism induces an isomorphism of `K₂` groups. -/
def equivOfRingEquiv (e : R ≃+* S) : AlgebraicK2 R ≃* AlgebraicK2 S :=
  (map e.toRingHom).toMulEquiv (map e.symm.toRingHom)
    (by rw [← map_comp]; simp)
    (by rw [← map_comp]; simp)

/-- `equivOfRingEquiv e` acts as `AlgebraicK2.map e.toRingHom`. -/
@[simp]
theorem equivOfRingEquiv_apply (e : R ≃+* S) (x : AlgebraicK2 R) :
    equivOfRingEquiv e x = map e.toRingHom x :=
  (rfl)

end Map

/-! ## Binary products -/

section Prod

variable (R) (S : Type*) [Ring S]

private theorem prodEquiv_symm_mem_ker (x : AlgebraicK2 R) (y : AlgebraicK2 S) :
    (SteinbergGroup.prodEquiv (ι := ℕ) (R := R) (S := S)
      (fun i j _ => ⟨max i j + 1, by omega, by omega⟩)).symm (x.1, y.1) ∈
      (SteinbergGroup.toStableGL (R × S)).ker := by
  let hnat : ∀ i j : ℕ, i ≠ j → ∃ k : ℕ, k ≠ i ∧ k ≠ j :=
    fun i j _ => ⟨max i j + 1, by omega, by omega⟩
  let e := SteinbergGroup.prodEquiv (ι := ℕ) (R := R) (S := S) hnat
  set z : SteinbergGroup ℕ (R × S) := e.symm (x.1, y.1)
  have hz_pair : (SteinbergGroup.map (RingHom.fst R S) z,
      SteinbergGroup.map (RingHom.snd R S) z) = (x.1, y.1) := by
    rw [← SteinbergGroup.prodEquiv_apply hnat z]
    exact e.apply_symm_apply (x.1, y.1)
  have hfst : SteinbergGroup.map (RingHom.fst R S) z = x.1 := congrArg Prod.fst hz_pair
  have hsnd : SteinbergGroup.map (RingHom.snd R S) z = y.1 := congrArg Prod.snd hz_pair
  obtain ⟨n, w, hw⟩ := SteinbergGroup.exists_ofFin z
  rw [MonoidHom.mem_ker, ← hw, SteinbergGroup.toStableGL_ofFin]
  suffices hgl : SteinbergGroup.toGL (Fin n) (R × S) w = 1 by rw [hgl, map_one]
  have hgl_fst : SteinbergGroup.toGL (Fin n) R (SteinbergGroup.map (RingHom.fst R S) w) = 1 := by
    apply StableGeneralLinearGroup.of_injective n
    rw [map_one, ← SteinbergGroup.toStableGL_ofFin, SteinbergGroup.ofFin_map, hw, hfst]
    exact MonoidHom.mem_ker.mp x.2
  have hgl_snd : SteinbergGroup.toGL (Fin n) S (SteinbergGroup.map (RingHom.snd R S) w) = 1 := by
    apply StableGeneralLinearGroup.of_injective n
    rw [map_one, ← SteinbergGroup.toStableGL_ofFin, SteinbergGroup.ofFin_map, hw, hsnd]
    exact MonoidHom.mem_ker.mp y.2
  ext i j
  · have h1 := congrArg (fun u : GL (Fin n) R => (u : Matrix (Fin n) (Fin n) R) i j) hgl_fst
    rw [SteinbergGroup.toGL_map] at h1
    simpa [Matrix.one_apply, apply_ite Prod.fst] using h1
  · have h2 := congrArg (fun u : GL (Fin n) S => (u : Matrix (Fin n) (Fin n) S) i j) hgl_snd
    rw [SteinbergGroup.toGL_map] at h2
    simpa [Matrix.one_apply, apply_ite Prod.snd] using h2

/-- `AlgebraicK2` preserves binary products of rings: `K₂(R × S) ≃* K₂(R) × K₂(S)`. -/
def prodEquiv : AlgebraicK2 (R × S) ≃* AlgebraicK2 R × AlgebraicK2 S :=
  let hnat : ∀ i j : ℕ, i ≠ j → ∃ k : ℕ, k ≠ i ∧ k ≠ j :=
    fun i j _ => ⟨max i j + 1, by omega, by omega⟩
  let e := SteinbergGroup.prodEquiv (ι := ℕ) (R := R) (S := S) hnat
  let fwd : AlgebraicK2 (R × S) →* AlgebraicK2 R × AlgebraicK2 S :=
    (map (RingHom.fst R S)).prod (map (RingHom.snd R S))
  let bwd : AlgebraicK2 R × AlgebraicK2 S →* AlgebraicK2 (R × S) :=
    (e.symm.toMonoidHom.comp ((subtype R).prodMap (subtype S))).codRestrict
      (SteinbergGroup.toStableGL (R × S)).ker fun ⟨x, y⟩ => by
        simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.coe_prodMap,
          Prod.map_apply, coe_subtype] using prodEquiv_symm_mem_ker R S x y
  fwd.toMulEquiv bwd
    (by
      ext z
      have h := e.symm_apply_apply z.1
      dsimp only [e] at h
      rw [SteinbergGroup.prodEquiv_apply] at h
      simpa [fwd, bwd, e] using h)
    (by
      ext ⟨x, y⟩
      · have h := e.apply_symm_apply (x.1, y.1)
        dsimp only [e] at h
        rw [SteinbergGroup.prodEquiv_apply] at h
        simpa [fwd, bwd, e] using congrArg Prod.fst h
      · have h := e.apply_symm_apply (x.1, y.1)
        dsimp only [e] at h
        rw [SteinbergGroup.prodEquiv_apply] at h
        simpa [fwd, bwd, e] using congrArg Prod.snd h)

/-- `AlgebraicK2.prodEquiv` applies the two projection maps `K₂(R × S) →* K₂(R)` and
`K₂(R × S) →* K₂(S)`. -/
@[simp]
theorem prodEquiv_apply {R S : Type*} [Ring R] [Ring S] (x : AlgebraicK2 (R × S)) :
    prodEquiv R S x = (map (RingHom.fst R S) x, map (RingHom.snd R S) x) :=
  (rfl)

end Prod

end AlgebraicK2

/-! ## Exact sequence `1 → K₂(R) → St(R) → GL_∞(R) → K₁(R) → 1` -/

/-- Exactness at `GL_∞(R)` of the four-term sequence `1 → K₂(R) → St(R) → GL_∞(R) → K₁(R) → 1`:
the image of `SteinbergGroup.toStableGL R` equals the kernel of the projection
`GL_∞(R) → K₁(R)`. -/
theorem SteinbergGroup.range_toStableGL_eq_ker_abelianization {R : Type*} [Ring R] :
    (SteinbergGroup.toStableGL R).range =
      (Group.Abelianization.of : StableGeneralLinearGroup R →* AlgebraicK1 R).ker := by
  rw [SteinbergGroup.range_toStableGL, AlgebraicK1.ker_of]

end TauCeti
