/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.RegularWreathProduct
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import TauCeti.Algebra.GroupAction.Trivial
public import TauCeti.GroupTheory.GroupExtension.FactorSetOfSection

/-!
# The wreath product `C₂ ≀ C₂` and the extension `1 → C₂ → D₁₆ → C₂ ≀ C₂ → 1`

The regular wreath product `C₂ ≀ C₂` of the cyclic group of order two by itself is the dihedral
group of order eight. This file reads it on coordinates: an element is a triple `(a, b, c)` of
elements of `ZMod 2`, where `(a, b)` is the base function, evaluated at the identity and at the
generator of the top factor, and `c` is the top coordinate. The multiplication is

```text
(a, b, c) (a', b', c') = (a + a' + c (a' + b'), b + b' + c (a' + b'), c + c'),
```

so a top coordinate `c = 1` exchanges the two base coordinates of the right factor
(`TauCeti.WreathC2.mk_mul_mk`).

The dihedral group `D₁₆ = ⟨r, f⟩` of order sixteen, Mathlib's `DihedralGroup 8` with `f = sr 0`,
maps onto `C₂ ≀ C₂` by `r ↦ u s = (1, 0, 1)` and `f ↦ s = (0, 0, 1)`, with kernel its centre
`{1, r⁴}`. This makes `D₁₆` a central extension of `C₂ ≀ C₂` by `C₂`
(`TauCeti.wreathD16Extension`). Its factor set at the section `(u s)ⁱ sʲ ↦ rⁱ fʲ` is a
`ZMod 2`-valued `2`-cocycle of `C₂ ≀ C₂` with trivial action, computed explicitly on coordinates by
`TauCeti.wreathD16Cocycle_apply`.

By Kahn and Serre (references below), the class of this cocycle is the second Stiefel–Whitney
class of the signed-permutation representation `C₂ ≀ C₂ ⊂ O₂`; that identification is not
formalised here. The cocycle is the universal case of the index-two Evens norm: the graph cochain
of the tautological character of the base group differs from it by an explicit coboundary
(`TauCeti.ContCohomology.evensGraphCochain_wreath`).

## Main definitions

* `TauCeti.WreathC2`: the regular wreath product `C₂ ≀ C₂`, with the constructor
  `TauCeti.WreathC2.mk` and the coordinates `TauCeti.WreathC2.coordA`, `TauCeti.WreathC2.coordB`,
  `TauCeti.WreathC2.coordC`.
* `TauCeti.wreathSwap`: the swap `s = (0, 0, 1)`, the generator of the top factor.
* `TauCeti.dihedralToWreath`: the quotient map `D₁₆ → C₂ ≀ C₂`.
* `TauCeti.wreathD16Extension`: `D₁₆` as an extension of `C₂ ≀ C₂` by `C₂`.
* `TauCeti.wreathSection`: the section `(u s)ⁱ sʲ ↦ rⁱ fʲ` of that extension.
* `TauCeti.wreathD16Cocycle`: its factor set, valued in `ZMod 2`.

## Main results

* `TauCeti.WreathC2.mk_mul_mk`: the multiplication on coordinates.
* `TauCeti.dihedralToWreath_eq_one_iff`: the kernel of `D₁₆ → C₂ ≀ C₂` is `{1, r⁴}`.
* `TauCeti.wreathSection_apply`: the section on coordinates.
* `TauCeti.wreathSection_mul_wreathSection`: the section is multiplicative up to the factor set.
* `TauCeti.wreathD16Cocycle_apply`: the factor set on coordinates.
* `TauCeti.wreathD16Cocycle_isCocycle`: the factor set is a `2`-cocycle for the trivial action.

## References

* B. Kahn, *Classes de Stiefel-Whitney de formes quadratiques et de représentations galoisiennes
  réelles*, Invent. Math. **78** (1984), 223–256, th. I.4.2 and Remarque II.2.3: the dihedral
  group of order eight as `C₂ ≀ C₂` with its tautological character, and the extension `D₁₆`.
* J.-P. Serre, *L'invariant de Witt de la forme Tr(x²)*, Comment. Math. Helv. **59** (1984),
  651–676.
-/

public section

namespace TauCeti

open Multiplicative

/-- **The wreath product `C₂ ≀ C₂`**, Mathlib's regular wreath product of the cyclic group of order
two, written multiplicatively, by itself. It is the dihedral group of order eight; its elements are
read on the coordinates `TauCeti.WreathC2.coordA`, `TauCeti.WreathC2.coordB` and
`TauCeti.WreathC2.coordC`. -/
abbrev WreathC2 : Type := Multiplicative (ZMod 2) ≀ᵣ Multiplicative (ZMod 2)

namespace WreathC2

/-- The element of `C₂ ≀ C₂` with coordinates `(a, b, c)`: the base function takes the value `a`
at the identity and `b` at the generator, and the top coordinate is `c`. -/
def mk (a b c : ZMod 2) : WreathC2 :=
  ⟨fun x => ofAdd (if x = 1 then a else b), ofAdd c⟩

/-- The first coordinate of an element of `C₂ ≀ C₂`: its base function at the identity. -/
def coordA (g : WreathC2) : ZMod 2 := toAdd (g.left 1)

/-- The second coordinate of an element of `C₂ ≀ C₂`: its base function at the generator. -/
def coordB (g : WreathC2) : ZMod 2 := toAdd (g.left (ofAdd 1))

/-- The third coordinate of an element of `C₂ ≀ C₂`: its top coordinate. -/
def coordC (g : WreathC2) : ZMod 2 := toAdd g.right

/-- The first coordinate of `(a, b, c)` is `a`. -/
@[simp]
theorem coordA_mk (a b c : ZMod 2) : coordA (mk a b c) = a := by
  simp [coordA, mk]

/-- The second coordinate of `(a, b, c)` is `b`. -/
@[simp]
theorem coordB_mk (a b c : ZMod 2) : coordB (mk a b c) = b := by
  simp [coordB, mk]

/-- The third coordinate of `(a, b, c)` is `c`. -/
@[simp]
theorem coordC_mk (a b c : ZMod 2) : coordC (mk a b c) = c := by
  simp [coordC, mk]

/-- Every element of `C₂ ≀ C₂` is the element with its own coordinates. -/
theorem mk_coordA_coordB_coordC (g : WreathC2) : mk (coordA g) (coordB g) (coordC g) = g := by
  obtain ⟨f, q⟩ := g
  refine RegularWreathProduct.ext (funext fun x => ?_) (by simp [mk, coordC])
  obtain rfl | rfl : x = 1 ∨ x = ofAdd 1 := by revert x; decide
  · simp [mk, coordA]
  · simp [mk, coordB]

/-- Elements of `C₂ ≀ C₂` with the same coordinates are equal. -/
@[ext]
theorem ext {g h : WreathC2} (hA : coordA g = coordA h) (hB : coordB g = coordB h)
    (hC : coordC g = coordC h) : g = h := by
  rw [← mk_coordA_coordB_coordC g, ← mk_coordA_coordB_coordC h, hA, hB, hC]

/-- Two elements given by coordinates are equal exactly when their coordinates are. -/
theorem mk_inj {a b c a' b' c' : ZMod 2} : mk a b c = mk a' b' c' ↔ a = a' ∧ b = b' ∧ c = c' :=
  ⟨fun h => ⟨by simpa using congrArg coordA h, by simpa using congrArg coordB h,
    by simpa using congrArg coordC h⟩, by rintro ⟨rfl, rfl, rfl⟩; rfl⟩

/-- The identity of `C₂ ≀ C₂` is `(0, 0, 0)`. -/
@[simp]
theorem mk_zero : mk 0 0 0 = 1 :=
  RegularWreathProduct.ext (funext fun x => by simp [mk]) rfl

/-- The first coordinate of the identity is `0`. -/
@[simp]
theorem coordA_one : coordA 1 = 0 := by rw [← mk_zero, coordA_mk]

/-- The second coordinate of the identity is `0`. -/
@[simp]
theorem coordB_one : coordB 1 = 0 := by rw [← mk_zero, coordB_mk]

/-- The third coordinate of the identity is `0`. -/
@[simp]
theorem coordC_one : coordC 1 = 0 := by rw [← mk_zero, coordC_mk]

/-- **The multiplication of `C₂ ≀ C₂` on coordinates:** the top coordinate of the left factor
exchanges the two base coordinates of the right factor. -/
theorem mk_mul_mk (a b c a' b' c' : ZMod 2) :
    mk a b c * mk a' b' c' =
      mk (a + a' + c * (a' + b')) (b + b' + c * (a' + b')) (c + c') := by
  refine RegularWreathProduct.ext (funext fun x => ?_) rfl
  simp only [RegularWreathProduct.mul_left, mk, Pi.mul_apply]
  revert a b c a' b' c' x
  decide

/-- The first coordinate of a product. -/
@[simp]
theorem coordA_mul (g h : WreathC2) :
    coordA (g * h) = coordA g + coordA h + coordC g * (coordA h + coordB h) := by
  rw [← mk_coordA_coordB_coordC g, ← mk_coordA_coordB_coordC h, mk_mul_mk]
  simp only [coordA_mk, coordB_mk, coordC_mk]

/-- The second coordinate of a product. -/
@[simp]
theorem coordB_mul (g h : WreathC2) :
    coordB (g * h) = coordB g + coordB h + coordC g * (coordA h + coordB h) := by
  rw [← mk_coordA_coordB_coordC g, ← mk_coordA_coordB_coordC h, mk_mul_mk]
  simp only [coordA_mk, coordB_mk, coordC_mk]

/-- The third coordinate is additive: it is the projection to the top factor. -/
@[simp]
theorem coordC_mul (g h : WreathC2) : coordC (g * h) = coordC g + coordC h := by
  rw [← mk_coordA_coordB_coordC g, ← mk_coordA_coordB_coordC h, mk_mul_mk]
  simp only [coordC_mk]

/-- The inverse on coordinates: `(a, b, 0)` is its own inverse, and `(a, b, 1)⁻¹ = (b, a, 1)`. -/
theorem inv_mk (a b c : ZMod 2) :
    (mk a b c)⁻¹ = mk (a + c * (a + b)) (b + c * (a + b)) c := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [mk_mul_mk, ← mk_zero, mk_inj]
  revert a b c
  decide

/-- The first coordinate of an inverse. -/
@[simp]
theorem coordA_inv (g : WreathC2) : coordA g⁻¹ = coordA g + coordC g * (coordA g + coordB g) := by
  conv_lhs => rw [← mk_coordA_coordB_coordC g]
  rw [inv_mk, coordA_mk]

/-- The second coordinate of an inverse. -/
@[simp]
theorem coordB_inv (g : WreathC2) : coordB g⁻¹ = coordB g + coordC g * (coordA g + coordB g) := by
  conv_lhs => rw [← mk_coordA_coordB_coordC g]
  rw [inv_mk, coordB_mk]

/-- The third coordinate of an inverse. -/
@[simp]
theorem coordC_inv (g : WreathC2) : coordC g⁻¹ = coordC g := by
  conv_lhs => rw [← mk_coordA_coordB_coordC g]
  rw [inv_mk, coordC_mk]

end WreathC2

open WreathC2

/-- **The base group `C₂ × C₂` of `C₂ ≀ C₂`**, the kernel of the projection to the top factor: the
elements with third coordinate `0`. It has index two (`TauCeti.index_wreathBase`). -/
def wreathBase : Subgroup WreathC2 := RegularWreathProduct.rightHom.ker

/-- The base group consists of the elements with third coordinate `0`. -/
theorem mem_wreathBase_iff {g : WreathC2} : g ∈ wreathBase ↔ coordC g = 0 := by
  simp [wreathBase, coordC, MonoidHom.mem_ker, RegularWreathProduct.rightHom]

/-- The elements outside the base group are those with third coordinate `1`. -/
theorem notMem_wreathBase_iff {g : WreathC2} : g ∉ wreathBase ↔ coordC g = 1 := by
  rw [mem_wreathBase_iff]
  generalize coordC g = c
  revert c
  decide

/-- **The swap `s = (0, 0, 1)` of `C₂ ≀ C₂`**, the generator of the top factor. It lies outside the
base group, and multiplying by it on the left exchanges the two base coordinates. -/
def wreathSwap : WreathC2 := mk 0 0 1

/-- The first coordinate of the swap is `0`. -/
@[simp]
theorem coordA_wreathSwap : coordA wreathSwap = 0 := coordA_mk 0 0 1

/-- The second coordinate of the swap is `0`. -/
@[simp]
theorem coordB_wreathSwap : coordB wreathSwap = 0 := coordB_mk 0 0 1

/-- The third coordinate of the swap is `1`. -/
@[simp]
theorem coordC_wreathSwap : coordC wreathSwap = 1 := coordC_mk 0 0 1

/-- The swap lies outside the base group. -/
theorem wreathSwap_notMem_wreathBase : wreathSwap ∉ wreathBase :=
  notMem_wreathBase_iff.2 coordC_wreathSwap

/-- The base group of `C₂ ≀ C₂` has index two. -/
theorem index_wreathBase : wreathBase.index = 2 := by
  rw [wreathBase, Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective _
    (fun q => ⟨RegularWreathProduct.inl q, RegularWreathProduct.fun_id q⟩), Subgroup.card_top,
    Nat.card_eq_fintype_card]
  rfl

/-- **The tautological character of the base group of `C₂ ≀ C₂`**, its first coordinate. -/
def wreathTautological : wreathBase →* Multiplicative (ZMod 2) where
  toFun g := ofAdd (coordA (g : WreathC2))
  map_one' := by simp
  map_mul' g h := by
    simp [mem_wreathBase_iff.1 g.2, ofAdd_add]

/-- The tautological character of an element of the base group is its first coordinate. -/
@[simp]
theorem toAdd_wreathTautological (g : wreathBase) :
    toAdd (wreathTautological g) = coordA (g : WreathC2) := (rfl)

open DihedralGroup

/-- The underlying function of `TauCeti.dihedralToWreath`: `rⁱ ↦ (u s)ⁱ` and `f rⁱ ↦ s (u s)ⁱ`,
with `u s = (1, 0, 1)` and `s = (0, 0, 1)`. -/
private def dihedralToWreathFun : DihedralGroup 8 → WreathC2
  | .r i => mk 1 0 1 ^ i.val
  | .sr i => mk 0 0 1 * mk 1 0 1 ^ i.val

/-- **The quotient map `D₁₆ → C₂ ≀ C₂`**, `r ↦ u s = (1, 0, 1)` and `f = sr 0 ↦ s = (0, 0, 1)`.
Its kernel is the centre `{1, r⁴}` of `D₁₆` (`TauCeti.dihedralToWreath_eq_one_iff`). -/
def dihedralToWreath : DihedralGroup 8 →* WreathC2 where
  toFun := dihedralToWreathFun
  map_one' := by ext <;> decide +kernel
  map_mul' x y := by ext <;> revert x y <;> decide +kernel

/-- The rotation `r` of `D₁₆` maps to `u s = (1, 0, 1)`. -/
theorem dihedralToWreath_r_one : dihedralToWreath (r 1) = mk 1 0 1 := by
  ext <;> decide +kernel

/-- The reflection `f = sr 0` of `D₁₆` maps to the swap `s = (0, 0, 1)`. -/
theorem dihedralToWreath_sr_zero : dihedralToWreath (sr 0) = wreathSwap := by
  ext <;> decide +kernel

/-- **The kernel of `D₁₆ → C₂ ≀ C₂` is the centre `{1, r⁴}`.** -/
theorem dihedralToWreath_eq_one_iff (x : DihedralGroup 8) :
    dihedralToWreath x = 1 ↔ x = 1 ∨ x = r 4 := by
  rw [WreathC2.ext_iff]
  revert x
  decide +kernel

/-- The section `(u s)ⁱ sʲ ↦ rⁱ fʲ` on coordinates, for `0 ≤ i < 4` and `0 ≤ j < 2`. -/
private def wreathSectionFun (a b c : ZMod 2) : DihedralGroup 8 :=
  if c = 0 then
    if a = 0 then (if b = 0 then r 0 else sr 5) else (if b = 0 then sr 7 else r 2)
  else
    if a = 0 then (if b = 0 then sr 0 else r 3) else (if b = 0 then r 1 else sr 6)

private theorem dihedralToWreath_wreathSectionFun (g : WreathC2) :
    dihedralToWreath (wreathSectionFun (coordA g) (coordB g) (coordC g)) = g := by
  conv_rhs => rw [← mk_coordA_coordB_coordC g]
  generalize coordA g = a
  generalize coordB g = b
  generalize coordC g = c
  rw [WreathC2.ext_iff, coordA_mk, coordB_mk, coordC_mk]
  revert a b c
  decide +kernel

/-- `D₁₆ → C₂ ≀ C₂` is surjective. -/
theorem dihedralToWreath_surjective : Function.Surjective dihedralToWreath :=
  fun g => ⟨_, dihedralToWreath_wreathSectionFun g⟩

/-- The inclusion of the centre `{1, r⁴}` of `D₁₆`, `C₂ → D₁₆`, `x ↦ r^{4x}`. -/
private def dihedralCentreIncl : Multiplicative (ZMod 2) →* DihedralGroup 8 where
  toFun x := r (4 * (toAdd x).val)
  map_one' := by decide
  map_mul' x y := by revert x y; decide

/-- **`D₁₆` as an extension of `C₂ ≀ C₂` by `C₂`**: the kernel `C₂` is included as the centre
`{1, r⁴}` of `D₁₆`, and the projection is `TauCeti.dihedralToWreath`. The extension is central. -/
def wreathD16Extension :
    GroupExtension (Multiplicative (ZMod 2)) (DihedralGroup 8) WreathC2 where
  inl := dihedralCentreIncl
  rightHom := dihedralToWreath
  inl_injective x y := by revert x y; decide
  range_inl_eq_ker_rightHom := by
    ext x
    rw [MonoidHom.mem_range, MonoidHom.mem_ker, dihedralToWreath_eq_one_iff]
    revert x
    decide
  rightHom_surjective := dihedralToWreath_surjective

/-- The projection of `TauCeti.wreathD16Extension` is `TauCeti.dihedralToWreath`. -/
@[simp]
theorem wreathD16Extension_rightHom : wreathD16Extension.rightHom = dihedralToWreath := (rfl)

/-- The kernel of `TauCeti.wreathD16Extension` is included as `x ↦ r^{4x}`. -/
theorem wreathD16Extension_inl_apply (x : Multiplicative (ZMod 2)) :
    wreathD16Extension.inl x = r (4 * (toAdd x).val) := (rfl)

/-- **The section `(u s)ⁱ sʲ ↦ rⁱ fʲ` of `D₁₆ → C₂ ≀ C₂`**, for `0 ≤ i < 4` and `0 ≤ j < 2`,
with `u s = (1, 0, 1)`, `s = (0, 0, 1)` and `f = sr 0`. It sends the identity to the identity. -/
def wreathSection : wreathD16Extension.Section where
  toFun g := wreathSectionFun (coordA g) (coordB g) (coordC g)
  rightInverse_rightHom := dihedralToWreath_wreathSectionFun

/-- **The section on coordinates.** With `g = (a, b, c)`, `σ g` is the element `rⁱ fʲ` of `D₁₆`
lifting `g = (u s)ⁱ sʲ`, written in Mathlib's `r`/`sr` normal form (`f = sr 0`). -/
theorem wreathSection_apply (g : WreathC2) :
    wreathSection g =
      if coordC g = 0 then
        if coordA g = 0 then (if coordB g = 0 then r 0 else sr 5)
        else (if coordB g = 0 then sr 7 else r 2)
      else
        if coordA g = 0 then (if coordB g = 0 then sr 0 else r 3)
        else (if coordB g = 0 then r 1 else sr 6) :=
  (rfl)

/-- The section is a right inverse of `D₁₆ → C₂ ≀ C₂`. -/
@[simp]
theorem dihedralToWreath_wreathSection (g : WreathC2) : dihedralToWreath (wreathSection g) = g :=
  wreathSection.rightInverse_rightHom g

/-- The section is normalized: it sends the identity to the identity. -/
theorem wreathSection_one : wreathSection 1 = 1 := by
  rw [wreathSection_apply, coordA_one, coordB_one, coordC_one]
  decide

/-- **The `D₁₆` extension cocycle** `c_{D₁₆}`: the factor set
`σ g · σ h · σ (g h)⁻¹ ∈ {1, r⁴} ≅ C₂` of the section `σ = TauCeti.wreathSection` of
`TauCeti.wreathD16Extension`, read in `ZMod 2`. Its value on coordinates is
`TauCeti.wreathD16Cocycle_apply`. -/
noncomputable def wreathD16Cocycle (q : WreathC2 × WreathC2) : ZMod 2 :=
  toAdd (GroupExtension.factorSetFun wreathSection q)

/-- **The section is multiplicative up to the factor set:**
`σ g · σ h = r^{4 c(g, h)} · σ (g h)`. -/
theorem wreathSection_mul_wreathSection (g h : WreathC2) :
    wreathSection g * wreathSection h =
      r (4 * (wreathD16Cocycle (g, h)).val) * wreathSection (g * h) :=
  GroupExtension.section_mul wreathSection g h

/-- **The `D₁₆` extension cocycle on coordinates.** With `g = (a, b, c)` and `h = (a', b', c')`,
`c_{D₁₆} (g, h) = a b' + c (a' + b') + a c (a' + b') + c a' b'`. -/
theorem wreathD16Cocycle_apply (g h : WreathC2) :
    wreathD16Cocycle (g, h) =
      coordA g * coordB h + coordC g * (coordA h + coordB h) +
        coordA g * coordC g * (coordA h + coordB h) + coordC g * coordA h * coordB h := by
  have key := wreathSection_mul_wreathSection g h
  simp only [wreathSection_apply, coordA_mul, coordB_mul, coordC_mul] at key
  generalize wreathD16Cocycle (g, h) = z at key ⊢
  generalize coordA g = a at key ⊢
  generalize coordB g = b at key ⊢
  generalize coordC g = c at key ⊢
  generalize coordA h = a' at key ⊢
  generalize coordB h = b' at key ⊢
  generalize coordC h = c' at key ⊢
  revert a b c a' b' c' z
  decide +kernel

/-- **The `D₁₆` extension cocycle is a `2`-cocycle**, in the trivial-action form of
`groupCohomology.IsCocycle₂`; the action is trivial because the extension is central. -/
theorem wreathD16Cocycle_isCocycle (g h j : WreathC2) :
    wreathD16Cocycle (g * h, j) + wreathD16Cocycle (g, h) =
      wreathD16Cocycle (h, j) + wreathD16Cocycle (g, h * j) := by
  let := trivialMulDistribMulAction WreathC2 (Multiplicative (ZMod 2))
  have hcentre : wreathD16Extension.inl.range ≤ Subgroup.center (DihedralGroup 8) := by
    rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_center_iff]
    revert x
    decide
  have hact := (GroupExtension.inducesAction_iff_smul_eq_self hcentre).2 fun _ _ =>
    trivialMulDistribMulAction_smul _ _
  have key := GroupExtension.isMulCocycle₂_factorSetFun wreathSection hact g h j
  rw [trivialMulDistribMulAction_smul] at key
  exact congrArg toAdd key

end TauCeti
