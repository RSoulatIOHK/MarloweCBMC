{-# LANGUAGE OverloadedStrings #-}

import Text.Blaze.Html5 as H
import Text.Blaze.Html5.Attributes as A
import Text.Blaze.Html.Renderer.Text (renderHtml)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO

-- Function to fill the invoice template
fillInvoiceTemplate :: T.Text -> String -> String -> String -> String -> String -> String -> String -> String -> String -> String -> String -> String -> String -> String -> String -> String -> String -> String -> String -> String -> String -> String -> String -> T.Text
fillInvoiceTemplate template invoiceNumber date billedCompany billedAddress billedPhone lineNum item itemDescription priceLine qty totalLinePrice numAda applicationWalletAddress transactionId conversionRate priceVatLess totalVat total footer tAndC =
  renderHtml $ do
    let parsedTemplate = preEscapedToHtml $ T.unpack template
    H.docTypeHtml $ do
      H.head $ do
        H.title "Invoice Template"
        H.link ! A.rel "stylesheet" ! A.type_ "text/css" ! A.href "G:\\IOG\\invoicing\\template\\styles.css"
      H.body $ do
        parsedTemplate
        H.div ! A.class_ "wrapper" $ do
          H.div ! A.class_ "invoice_wrapper" $ do
            H.div ! A.class_ "header" $ do
              H.div ! A.class_ "logo_invoice_wrap" $ do
                H.div ! A.class_ "logo_sec" $ do
                  H.img ! A.src "G:\\IOG\\invoicing\\iohk-symbol-big.png" ! A.alt "IOHK logo" ! A.width "25%" ! A.height "auto"
                  H.div ! A.class_ "title_wrap" $ do
                    H.p ! A.class_ "title bold" $ "IOG Singapore Pte Ltd"
                    H.p ! A.class_ "sub_title" $ "4 Battery Road"
                    H.p ! A.class_ "sub_title" $ "25-01 Bank of China Building"
                    H.p ! A.class_ "sub_title" $ "Singapore 049908"
                    H.p ! A.class_ "sub_title" $ "Singapore"
                H.div ! A.class_ "invoice_sec" $ do
                  H.p ! A.class_ "invoice bold" $ "INVOICE"
                  H.p ! A.class_ "invoice_no" $ do
                    H.span ! A.class_ "bold" $ "Invoice"
                    H.span $ toHtml invoiceNumber
                  H.p ! A.class_ "date" $ do
                    H.span ! A.class_ "bold" $ "Date"
                    H.span $ toHtml date
            H.div ! A.class_ "body" $ do
              H.div ! A.class_ "main_table" $ do
                H.div ! A.class_ "table_header" $ do
                  H.div ! A.class_ "row" $ do
                    H.div ! A.class_ "col col_no" $ "NO."
                    H.div ! A.class_ "col col_des" $ "ITEM DESCRIPTION"
                    H.div ! A.class_ "col col_price" $ "RATE"
                    H.div ! A.class_ "col col_qty" $ "QTY"
                    H.div ! A.class_ "col col_total" $ "TOTAL"
                H.div ! A.class_ "table_body" $ do
                  H.div ! A.class_ "row" $ do
                    H.div ! A.class_ "col col_no" $ do
                      H.p $ toHtml lineNum
                    H.div ! A.class_ "col col_des" $ do
                      H.p ! A.class_ "bold" $ toHtml item
                      H.p $ toHtml itemDescription
                    H.div ! A.class_ "col col_price" $ do
                      H.p $ toHtml priceLine
                    H.div ! A.class_ "col col_qty" $ do
                      H.p $ toHtml qty
                    H.div ! A.class_ "col col_total" $ do
                      H.p $ toHtml totalLinePrice
              H.div ! A.class_ "paymethod_grandtotal_wrap" $ do
                H.div ! A.class_ "paymethod_sec" $ do
                  H.p ! A.class_ "bold" $ "Payment Method"
                  H.p $ toHtml (numAda ++ " Ada sent to " ++ applicationWalletAddress)
                  H.p $ toHtml ("Transaction ID: " ++ transactionId)
                  H.p $ toHtml ("Conversion rate: " ++ conversionRate)
                H.div ! A.class_ "grandtotal_sec" $ do
                  H.p ! A.class_ "bold" $ do
                    H.span $ "SUB TOTAL"
                    H.span $ toHtml priceVatLess
                  H.p $ do
                    H.span $ "Tax Vat"
                    H.span $ toHtml totalVat
                  H.p ! A.class_ "bold" $ do
                    H.span $ "Total"
                    H.span $ toHtml total
              H.div ! A.class_ "footer" $ do
                H.p $ toHtml footer
                H.div ! A.class_ "terms" $ do
                  H.p ! A.class_ "tc bold" $ "Terms & Conditions"
                  H.p $ toHtml tAndC

-- Example usage
main :: IO ()
main = do
  -- Read the template from a file
  template <- TIO.readFile "invoice_template.html"

  let filledInvoice = fillInvoiceTemplate template "INV-001" "2023-07-13" "Billed Company" "Billed Address" "Billed Phone" "1" "Item" "Item Description" "Price" "Quantity" "Total Line Price" "Num Ada" "Application Wallet Address" "Transaction ID" "Conversion Rate" "Price VAT Less" "Total VAT" "Total" "Footer" "Terms and Conditions"
  TIO.putStr filledInvoice
