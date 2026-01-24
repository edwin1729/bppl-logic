-- Trying to get the product operation with too much additional stuff in `MeasCat`
-- What claude code came up with.
open CategoryTheory.Limits in
instance (X Y : MeasCat) : HasBinaryProduct X Y :=
  HasLimit.mk
    { cone := BinaryFan.mk
        (P := MeasCat.of (X × Y))
        ⟨Prod.fst, measurable_fst⟩
        ⟨Prod.snd, measurable_snd⟩
      isLimit := BinaryFan.isLimitMk
        (fun s => ⟨fun x => (s.fst x, s.snd x), s.fst.2.prod s.snd.2⟩)
        (fun _ => rfl)
        (fun _ => rfl)
        (fun _ _ h₁ h₂ => Subtype.ext <| funext fun x =>
          Prod.ext (congrFun (congrArg Subtype.val h₁) x)
                   (congrFun (congrArg Subtype.val h₂) x)) }
